-- Prove2me | Theorems.Thm_TopkisRation_Backlog_theorem_3
-- name    : TopkisRation.Backlog.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:35.015107+00:00
-- url     : https://prove2.me/theorems/05939232-2be3-4138-9207-701122889262
-- title:
--   Theorem 3, p. 172 — under full backlogging and independent classes, z̄_{t+1}^j ignores the penalties of classes below j and the demands of classes 1, …, j
-- statement:
--   Consider two instances $M$ and $M'$ of the inventory model of Topkis (1968, §1), both satisfying its standing assumptions, with the same number $k$ of intervals, and fix an interval index $t$ with $t + 1 \le k$ and a demand class $j$. Assume that in both instances
--
--   1. there is complete backlogging in intervals $1,\dots,t+1$: $a_{t+1} = a_t = \dots = a_1 = 1$;
--   2. the demands of different classes are independent in each interval.
--
--   Assume further that $M$ and $M'$ have the same salvage costs $v_1, v_2$, the same holding costs $h_i$ and the same penalties $p_i^m$ of the classes $m \ge j$ for $i \le t+1$, and the same demand distribution of every class $m > j$ in every interval; they may differ in the penalties of the classes $m \le j-1$ and in the demand distributions of the classes $m \le j$. Then:
--
--   (a) for every $z \ge 0$, every class $s > j$, every $w \ge 0$ and every $b \ge 0$ with $b^s > 0$,
--   $$
--   D_z^+ g_t(z, z\delta_j) = D_z^+ g'_t(z, z\delta_j), \qquad D_\varepsilon^+ g_t\big(w, \varepsilon(\delta_j - \delta_s) + b\big)\big|_{\varepsilon=0} = D_\varepsilon^+ g'_t\big(w, \varepsilon(\delta_j - \delta_s) + b\big)\big|_{\varepsilon=0};
--   $$
--
--   (b) the critical rationing levels of class $j$ in interval $t+1$ coincide:
--   $$
--   \bar z_{t+1}^j = \bar z_{t+1}^{\prime\, j},
--   $$
--   where $\bar z_{t+1}^j \in [0,\infty]$ is $+\infty$ if $w \mapsto p_{t+1}^j w + h_{t+1}(w) + g_t(w, w\delta_j)$ is strictly decreasing on $[0,\infty)$ and its smallest minimizer on $[0,\infty)$ otherwise, and likewise for $M'$.
--
--   Consequently, under full backlogging the class-$j$ critical rationing levels can be computed from a problem with only the classes $j,\dots,n$, with the class-$j$ demand replaced by any convenient distribution.
--
--   **Formalization Note** "Does not depend on" is stated as equality for two instances that agree on all other relevant data; data of intervals beyond $t+1$ and the ordering cost are unconstrained. Independence of the classes in each interval is `iIndepFun` of the coordinate maps, and agreement of the demand data is equality of the class-$m$ marginals for $m > j$. Part (b) is stated for any critical levels $z_1, z'_1$ of the two instances (values in $\mathbb R \cup \{+\infty\}$ described by the predicate `IsCriticalLevel`); such levels exist and are unique. The page writes "$\{p_i^m = 1 \le m \le j-1, \text{all } i\}$" for $\{p_i^m : 1 \le m \le j-1, \text{all } i\}$. $D^+$ is the extended-real right derivative.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 172, Theorem 3

import Mathlib
import Definitions.Def_TopkisRation_Backlog_Model

namespace TopkisRation.Backlog

open MeasureTheory ProbabilityTheory

variable {n : ℕ}

/-- Theorem 3, p. 172: with full backlogging in intervals 1, …, t + 1 and independent classes, for two
models that differ only in the penalties of classes 1, …, j − 1 and in the demand distributions of
classes 1, …, j, (a) the derivatives D_z⁺g_t(z, zδ_j) and D_ε⁺g_t(w, ε(δ_j − δ_s) + b)/ε = 0
(s > j, bˢ > 0) agree, and (b) the critical rationing levels z̄_{t+1}^j agree. -/
theorem theorem_3 (M M' : Model n) (hM : M.Standing) (hM' : M'.Standing)
    (t : ℕ) (htk : t + 1 ≤ M.k) (hk : M'.k = M.k)
    (ha : ∀ i ∈ Finset.Icc 1 (t + 1), M.a i = 1) (ha' : ∀ i ∈ Finset.Icc 1 (t + 1), M'.a i = 1)
    (hind : ∀ i ∈ Finset.Icc 1 M.k, iIndepFun (fun m (x : Fin n → ℝ) => x m) (M.μ i))
    (hind' : ∀ i ∈ Finset.Icc 1 M.k, iIndepFun (fun m (x : Fin n → ℝ) => x m) (M'.μ i))
    (j : Fin n)
    (hh : ∀ i ∈ Finset.Icc 1 (t + 1), M'.h i = M.h i) (hv₁ : M'.v₁ = M.v₁) (hv₂ : M'.v₂ = M.v₂)
    (hp : ∀ i ∈ Finset.Icc 1 (t + 1), ∀ m, j ≤ m → M'.p i m = M.p i m)
    (hd : ∀ i ∈ Finset.Icc 1 M.k, ∀ m, j < m →
      (M'.μ i).map (fun x => x m) = (M.μ i).map (fun x => x m)) :
    (∀ z, 0 ≤ z →
      TopkisRation.Levels.rightDeriv (fun z => M.g t z (z • Pi.single j 1)) z =
        TopkisRation.Levels.rightDeriv (fun z => M'.g t z (z • Pi.single j 1)) z) ∧
    (∀ s : Fin n, j < s → ∀ w, 0 ≤ w → ∀ b : Fin n → ℝ, 0 ≤ b → 0 < b s →
      TopkisRation.Levels.rightDeriv (fun ε => M.g t w (ε • (Pi.single j 1 - Pi.single s 1) + b)) 0 =
        TopkisRation.Levels.rightDeriv (fun ε => M'.g t w (ε • (Pi.single j 1 - Pi.single s 1) + b)) 0) ∧
    (∀ z₁ z₁' : WithTop ℝ, TopkisRation.Levels.IsCriticalLevel (M.levelObj (t + 1) j) z₁ →
      TopkisRation.Levels.IsCriticalLevel (M'.levelObj (t + 1) j) z₁' → z₁ = z₁') := by sorry

end TopkisRation.Backlog
