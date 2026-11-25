-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sup_ratio_le_of_phase_zero
-- name    : ReciprocityTheory.ChartRestriction.G.I2.sup_ratio_le_of_phase_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:03:11.61385+00:00
-- url     : https://prove2.me/theorems/2493151a-1dbd-4b25-a37c-067d9d844fcc
-- title:
--   I2: sup ratio le of phase zero
-- statement:
--   The I2 construction uses the sup ratio le of phase zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SupRatioLeOfPhaseZero.lean#L147-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SupRatioLeOfPhaseZero.lean#L147-L204

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

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
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.sup_ratio_le_of_phase_zero [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hS : GSupStatement)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) (h0 : P.ph = 0) (a : Vsp X.dim) :
    Real.sqrt (X.ptN2 1 s fun _ => a) / Real.sqrt (X.l2 1 s) ≤ Real.exp P.p1 := by sorry
