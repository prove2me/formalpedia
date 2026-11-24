-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem33
-- name    : ShockWear.Inherit.Supplement.theorem33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:59:21.469281+00:00
-- url     : https://prove2.me/theorems/a90d0571-4e54-41c3-a32f-f2a721d915b5
-- title:
--   Theorem 3.3 (Murthy–Lientz) — nonnegative sums S_k give an IHR Poisson shock life
-- statement:
--   Let shocks arrive at rate $\lambda>0$, let $1=\bar P_0\geq\bar P_1\geq\cdots\geq0$ be the probabilities of surviving the first $k$ shocks, and let $\bar H$ be the Poisson shock survival function (1.1). Suppose that
--   $$S_k=\sum_{j=0}^k\binom kj\bigl[\bar P_{j+1}\bar P_{k-j+1}-\bar P_j\bar P_{k-j+2}\bigr]\;\geq\;0,\qquad k=0,1,\dots.$$
--   Then $\bar H$ has increasing hazard rate: for every $x>0$ and $s\leq t$,
--   $$\bar H(x+t)\,\bar H(s)\leq\bar H(x+s)\,\bar H(t).$$
--
--   The condition (3.13), due to Murthy and Lientz (1968), is strictly weaker than the PF₂ condition of Theorem 3.1 (3.2), so this theorem extends that result.
--
--   **Formalization Note** The IHR property is stated cross-multiplied on the whole real line, with $\bar H=1$ for $t<0$ as in (2.1); since $\bar P_0=1$ there is no atom at the origin. Nonnegativity and weak monotonicity of the $\bar P_k$ are the paper's standing assumption (2.2).
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 634, Theorem 3.3, display (3.13); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit.Supplement

/-- Theorem 3.3 (Murthy–Lientz): nonnegativity of the sums `S_k` of (3.13)
gives an IHR life law. -/
theorem theorem33 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hS : ∀ k, 0 ≤ ∑ j ∈ Finset.range (k + 1),
      (k.choose j : ℝ) * (P (j + 1) * P (k - j + 1) - P j * P (k - j + 2))) :
    IsIHR (ShockWear.CumDamage.shockSurv lam P) := by sorry

end ShockWear.Inherit.Supplement
