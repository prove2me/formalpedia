-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_eU_props
-- name    : ReciprocityTheory.ChartRestriction.G.I2.eU_props
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:50.906801+00:00
-- url     : https://prove2.me/theorems/4b086ed5-2f0f-4871-bb21-6d0505f6559e
-- title:
--   I2: e U props
-- statement:
--   The I2 construction uses the e U props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfNormLeTwo.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfNormLeTwo.lean#L20-L26

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardChoiceLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfNormLeTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
variable {E : Type} [Field E] [NumberField E]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.eU_props {dim : (E →+* ℂ) → ℕ} {n nb : ℕ} (bs : Fin nb → Block E n dim) (j : Fin nb)
    (a : Fin (bs j).i) : InPart (bs j).τ (eU bs j a) ∧ ‖eU bs j a‖ = 1 := by sorry
