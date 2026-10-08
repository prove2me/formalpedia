-- Prove2me | Theorems.Thm_TopkisRation_Levels_theorem_1
-- name    : TopkisRation.Levels.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:21.66909+00:00
-- url     : https://prove2.me/theorems/4e7b476a-acba-413b-b55a-03a27ab025d7
-- title:
--   Theorem 1, p. 167 — if each a_i ∈ {0, 1}: the rationing level policy is optimal, z̄_t¹ ≥ ⋯ ≥ z̄_tⁿ, and the differences in (c) ignore B¹, …, Bʲ
-- statement:
--   In the model of Topkis (1968, §1) under Assumptions (A)–(C), let $1\le t\le k$ and suppose that $a_i\in\{0,1\}$ for each $1\le i\le t$ (in every remaining interval there is either complete backlogging or no backlogging). Let $\bar z_t^1,\dots,\bar z_t^n\in[0,+\infty]$ be the critical rationing levels of interval $t$: $\bar z_t^j=+\infty$ if $\varphi_t^j(w)=p_t^jw+h_t(w)+g_{t-1}(w,a_tw\delta_j)$ is strictly decreasing on $[0,\infty)$, and $\bar z_t^j$ is the smallest minimizer of $\varphi_t^j$ on $[0,\infty)$ otherwise. Then:
--   1. **(a)** the rationing level policy is optimal in interval $t$: for every $z\ge0$ and $B\ge0$ the vector
--   $$
--   u^j=\big(B^{(j)}-z+\bar z_t^j\big)^+\wedge B^j\qquad(u^j=B^j\text{ if }\bar z_t^j=+\infty) \tag{7}
--   $$
--   is feasible in (1) and attains $f_t(z,B)$;
--   2. **(b)** $\bar z_t^1\ge\bar z_t^2\ge\cdots\ge\bar z_t^n$;
--   3. **(c)** for every $\varepsilon>0$ and every class $j$, the differences
--   $$
--   f_t(z,B)-f_t(z+\varepsilon,B+\varepsilon\delta_j)\qquad\text{and}\qquad g_t(z,b)-g_t(z+\varepsilon,b+\varepsilon\delta_j)
--   $$
--   do not depend on $B^1,\dots,B^j$ and $b^1,\dots,b^j$ respectively: for $z\ge0$ they take the same value at any two nonnegative vectors that agree in the classes $i>j$.
--
--   This is the main result of §1: under complete or no backlogging, the optimal rationing policy within an interval is described by $n$ numbers, one critical stock level per class, decreasing in the importance of the class. The hypothesis on $a_i$ cannot be dropped: the paper exhibits an example with $a_2\in(0,1)$ where no such description exists.
--
--   **Formalization Note.** Class $j$ is index $j-1$ of `Fin n`, so (b) is `Antitone`. The critical levels are taken as a hypothesis on a given family (the paper's "pick $\{\bar z_t^j\}$ such that"); such a family exists and is unique (milestone `criticalLevel_exists`). The page prints "$\bar z_t^1\ge\bar z_1^2\ge\cdots$" in the definition of (7), read $\bar z_t^2$. Optimality in (a) is over all feasible $u$ in (1), not among rationing level policies.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 167, Theorem 1 (with the definition of z̄_t^j and (7), p. 166)

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.Levels

theorem theorem_1 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k)
    (ha : ∀ i ∈ Finset.Icc 1 t, M.a i = 0 ∨ M.a i = 1)
    (zbar : Fin n → WithTop ℝ) (hz : ∀ j, IsCriticalLevel (M.levelObj t j) (zbar j)) :
    (∀ z, 0 ≤ z → ∀ B : Fin n → ℝ, 0 ≤ B →
        rationU zbar z B ∈ feasible z B ∧
        M.f t z B = M.obj t (M.g (t - 1)) z B (rationU zbar z B)) ∧
    Antitone zbar ∧
    (∀ ε : ℝ, 0 < ε → ∀ j : Fin n, ∀ z, 0 ≤ z →
      (∀ B B' : Fin n → ℝ, 0 ≤ B → 0 ≤ B' → (∀ i, j < i → B i = B' i) →
        M.f t z B - M.f t (z + ε) (B + ε • Pi.single j 1) =
          M.f t z B' - M.f t (z + ε) (B' + ε • Pi.single j 1)) ∧
      (∀ b b' : Fin n → ℝ, 0 ≤ b → 0 ≤ b' → (∀ i, j < i → b i = b' i) →
        M.g t z b - M.g t (z + ε) (b + ε • Pi.single j 1) =
          M.g t z b' - M.g t (z + ε) (b' + ε • Pi.single j 1))) := by sorry

end TopkisRation.Levels
