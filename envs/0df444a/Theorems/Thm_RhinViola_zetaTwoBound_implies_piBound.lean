-- Prove2me | Theorems.Thm_RhinViola_zetaTwoBound_implies_piBound
-- name    : RhinViola.zetaTwoBound_implies_piBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T22:28:49.446006+00:00
-- url     : https://prove2.me/theorems/6c1236d1-a539-4b4e-9c3c-63b2bb1291fa
-- title:
--   Transfer of any irrationality-measure upper bound from ζ(2)=π²/6 to π with exponent doubling
-- statement:
--   For any real m>0, if ζ(2)=π²/6 has an irrationality-measure upper bound m in the epsilon formulation (uniform for all integer numerators and positive natural denominators), then π has upper bound 2m in the corresponding PiIrrationality.UpperBound predicate. The proof uses the integer approximation p²/(6q²), factors π²−(p/q)²=(π−p/q)(π+p/q), splits rational approximations distant from π, and absorbs fixed multiplicative constants by a small epsilon power at sufficiently large denominators.
-- source:
--   Elementary square-root transfer of irrationality measure, applied to G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993) 85–109. Source-faithful reusable bridge for Prove2Me PiIrrationality.rhin_viola_bound (bda7f199-9603-4c9e-8825-e30a14d70f09). The deep assumption is independently formalised as child RhinViola.zetaTwoIrrationalityBound (bb98b323-fe68-49fe-a97c-b06c6157899b).

import Definitions.Def_PiIrrationality_UpperBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

theorem RhinViola.zetaTwoBound_implies_piBound (m : ℝ) (hm : 0 < m)
    (hz : ∀ ε : ℝ, 0 < ε →
      ∃ Q : ℕ, ∀ p : ℤ, ∀ q : ℕ, Q ≤ q → 0 < q →
        (q : ℝ) ^ (-(m + ε)) <
          |Real.pi ^ 2 / 6 - (p : ℝ) / (q : ℝ)|) :
    PiIrrationality.UpperBound (2 * m) := by sorry
