-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P39_fitted_interior_minimizer
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P39.fitted_interior_minimizer
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T09:46:55.788883+00:00
-- url     : https://prove2.me/theorems/a492bf3b-7e31-4d71-a5c4-60a5ca817807
-- title:
--   Margin minimizer in the fitted interior-block cost
-- statement:
--   Let $S\ge4$ be an integer. For integers $k\ge4$, $m\ge1$ with $km=S$, define the fitted interior-block cost
--
--   $$C(k,m)=(13k-8)\left((m+2)\frac{215}{100}-\frac{448}{100}\right)+\mathbf1_{m\ne1}(13k+3)\left(m\frac{69}{100}+\frac6{100}\right).$$
--
--   Then the feasible choice $(k,m)=(S,1)$ attains the minimum:
--
--   $$C(S,1)\le C(k,m)\qquad(km=S,\ k\ge4,\ m\ge1).$$
--
--   Here $S=(n-m_1-m_2-1)/2$ in the paper's application. The decimals define an exact rational surrogate for regression-based durations; this is not a theorem about optimal hardware time.
-- source:
--   Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates, arXiv:0712.3227v2, PDF p. 13, Interior-block minimizer in the fitted timing surrogate, Eq. (35)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39

namespace QAlgorithms.Papers.Independent.Intakethird100.P39

open scoped BigOperators

/-- PDF p.13, Eq. (35): for fixed S=km>=4, the feasible margin (S,1)
attains the minimum of the fitted cost. This is not optimal hardware time. -/
theorem fitted_interior_minimizer (S : ℕ) (hS : 4 ≤ S) :
    ∀ k m : ℕ, 4 ≤ k → 1 ≤ m → k * m = S →
      fittedInteriorCost S 1 ≤ fittedInteriorCost k m := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P39
