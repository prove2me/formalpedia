-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paU_contDiff
-- name    : ReciprocityTheory.ChartRestriction.G.I2.paU_contDiff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:35:48.528679+00:00
-- url     : https://prove2.me/theorems/3934b4da-6e96-4f7e-917f-bdc20ebd80ba
-- title:
--   I2: pa U cont Diff
-- statement:
--   The I2 construction uses the pa U cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L188-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L188-L193

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

theorem ReciprocityTheory.ChartRestriction.G.I2.paU_contDiff {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) : ContDiff ℂ (⊤ : ℕ∞) (paU q a F) := by sorry
