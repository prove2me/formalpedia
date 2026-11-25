-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pa_cd_sum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.pa_cd_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:39.524475+00:00
-- url     : https://prove2.me/theorems/c51f3cd8-a67d-4b78-8f32-ef7ff0cc15c5
-- title:
--   I2: pa cd sum
-- statement:
--   The I2 construction uses the pa cd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L229-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L229-L235

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

theorem ReciprocityTheory.ChartRestriction.G.I2.pa_cd_sum (s : Finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → ℂ) :
    ContDiff ℂ (⊤ : ℕ∞) (∑ β ∈ s, f β • paMono (ι := ι) β) := by sorry
