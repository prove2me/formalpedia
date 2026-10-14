-- Prove2me | Theorems.Thm_ThreeSumSharpTail_cost_regime_solve_3sum
-- name    : ThreeSumSharpTail.cost_regime_solve_3sum
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T17:55:03.55739+00:00
-- url     : https://prove2.me/theorems/421030db-0ca7-4fd3-af76-166d00b6be18
-- title:
--   Finite pruned program cost regime implies the 3SUM exponent
-- statement:
--   Fix the finite rational parameters G of the published pruned program, and rational a,s,r with 0<a<1 and 0<s<1/2. Suppose a uniform CostsWithinP certificate holds whenever 1<=D<=N^a, with preprocessing bound N^2(log D+1)^2/D^s and query bound D^(1/2-s)(log D+1). If the prime-selection and instance-construction exponents are strictly below 3-as/2, then integer 3SUM is solved on the word RAM in O(n^r) for every r>2-as/4. The conclusion uses the exact shared EndStatement model, including finite programs and all sufficiently large word widths.
-- source:
--   Algorithmic interface lemma derived from Xu, same manuscript, Sections 3-4, composed with the verified 3sum-apsp pruned program and parameterized all-edges/Exact-Triangle/3SUM reductions. This remaining semantic bridge is a separate open proof obligation, not an additional runtime hypothesis in the original certificate.

import Definitions.Def_APSP299791_Defs4
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumSharpTail.cost_regime_solve_3sum
    (G : Light.Sec4.RatParams) (a s r : ℚ)
    (ha0 : 0 < a) (ha1 : a < 1) (hs0 : 0 < s) (hsHalf : s < 1 / 2)
    (hcost : ∃ C : ℝ, 0 ≤ C ∧ ∀ N D : ℕ,
      1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
      Light.Sec4.CostsWithinP G C N D
        ((N : ℝ) ^ 2 * (Real.log D + 1) ^ 2 / (D : ℝ) ^ (s : ℝ))
        ((D : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log D + 1)))
    (hprime : Real.log 7 / Real.log 2 + 3 * (a : ℝ) / 2 < 3 - (a : ℝ) * s / 2)
    (hbuild : 2 + (a : ℝ) * (1 + (s : ℝ) / 2) < 3 - (a : ℝ) * s / 2)
    (hr : 2 - a * s / 4 < r) :
    EndStatement.ThreeSum.SolvedInTime r := by sorry
