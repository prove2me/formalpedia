-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polynomial_translate_innerProduct_bound
-- name    : ReciprocityTheory.ChartRestriction.G.I2.polynomial_translate_innerProduct_bound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:30:50.985224+00:00
-- url     : https://prove2.me/theorems/ff4d2369-b6f2-45c0-9655-b4468430df45
-- title:
--   I2: polynomial translate inner Product bound
-- statement:
--   The I2 construction uses the polynomial translate inner Product bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L107-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L107-L169

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.polynomial_translate_innerProduct_bound {q c : ℕ} (hq : 1 ≤ q) (a : EuclideanSpace ℂ ι) {F G : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    ‖paIP q (paU q a F) G‖ ≤ 2 ^ (1 + 3 * ((Fintype.card ι : ℝ) + c) / 2) *
      Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 16) * paN q F * paN q G := by sorry
