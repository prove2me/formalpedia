-- Prove2me | Theorems.Thm_TopkisRation_Backlog_theorem_3a
-- name    : TopkisRation.Backlog.theorem_3a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:06.314296+00:00
-- url     : https://prove2.me/theorems/42fbae12-56f3-4aaa-bd4b-61412fd97cd2
-- title:
--   Theorem 3 (a), p. 172 — under full backlogging, D_z⁺g_t(z, zδ_j) and D_ε⁺g_t(w, ε(δ_j − δ_s) + b) ignore lower-class penalties and class 1, …, j demands
-- statement:
--   Consider two instances $M$ and $M'$ of the inventory model of Topkis (1968, §1), both satisfying its standing assumptions, with the same number $k$ of intervals, and fix an interval index $t$ with $t + 1 \le k$ and a demand class $j$. Assume that in both instances
--
--   1. there is complete backlogging in intervals $1,\dots,t+1$: $a_{t+1} = a_t = \dots = a_1 = 1$;
--   2. the demands of different classes are independent in each interval.
--
--   Assume further that $M$ and $M'$ have the same salvage costs $v_1, v_2$, the same holding costs $h_i$ and the same penalties $p_i^m$ of the classes $m \ge j$ for $i \le t+1$, and the same demand distribution of every class $m > j$ in every interval. They may differ in the penalties $p_i^m$ of the classes $m \le j - 1$ and in the demand distributions of the classes $m \le j$. Then, writing $g_t$ and $g'_t$ for the expected cost functions of the two instances,
--
--   1. for every $z \ge 0$ the right derivatives along the ray $z \mapsto (z, z\delta_j)$ agree:
--   $$
--   D_z^+ g_t(z, z\delta_j) = D_z^+ g'_t(z, z\delta_j);
--   $$
--   2. for every class $s > j$, every $w \ge 0$ and every backlog vector $b \ge 0$ with $b^s > 0$,
--   $$
--   D_\varepsilon^+ g_t\big(w, \varepsilon(\delta_j - \delta_s) + b\big)\big|_{\varepsilon=0} = D_\varepsilon^+ g'_t\big(w, \varepsilon(\delta_j - \delta_s) + b\big)\big|_{\varepsilon=0}.
--   $$
--
--   In words: neither marginal quantity depends on the penalties of the classes below $j$ nor on the demand distributions of classes $1,\dots,j$. Part (b) of Theorem 3, the corresponding statement for the critical level $\bar z_{t+1}^j$, is derived from this.
--
--   **Formalization Note** "Does not depend on" is stated as equality for two instances that agree on all other relevant data. Independence of the classes in interval $i$ is `iIndepFun` of the coordinate maps under $\mu_i$; under it, the joint law is determined by the marginals, so the agreement of the demand data is the equality of the class-$m$ marginals for $m > j$. Data of intervals beyond $t+1$ (and the ordering cost) are left unconstrained, since $g_t$ and $\bar z_{t+1}^j$ do not use them. $D^+$ is the extended-real right derivative; $D_z^+ g_t(z, z\delta_j)$ moves the stock and the class-$j$ backlog together, as in the definition of $\bar z_{t+1}^j$ with $a_{t+1} = 1$.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 172, Theorem 3 (a)

import Mathlib
import Definitions.Def_TopkisRation_Backlog_Model

namespace TopkisRation.Backlog

open MeasureTheory ProbabilityTheory

variable {n : ℕ}

/-- Theorem 3 (a), p. 172: with full backlogging in intervals 1, …, t + 1 and independent classes,
the ray derivative D_z⁺g_t(z, zδ_j) and the swap derivative D_ε⁺g_t(w, ε(δ_j − δ_s) + b)/ε = 0
(s > j, bˢ > 0) are the same for two models that differ only in the penalties of classes 1, …, j − 1
and in the demand distributions of classes 1, …, j. -/
theorem theorem_3a (M M' : Model n) (hM : M.Standing) (hM' : M'.Standing)
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
        TopkisRation.Levels.rightDeriv (fun ε => M'.g t w (ε • (Pi.single j 1 - Pi.single s 1) + b)) 0) := by sorry

end TopkisRation.Backlog
