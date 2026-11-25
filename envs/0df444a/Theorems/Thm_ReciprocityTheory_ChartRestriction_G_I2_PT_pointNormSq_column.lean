-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_pointNormSq_column
-- name    : ReciprocityTheory.ChartRestriction.G.I2.PT.pointNormSq_column
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:49:51.70893+00:00
-- url     : https://prove2.me/theorems/2748eb78-3ba9-5c4c-8e2e-55d508f2ccf2
-- title:
--   PT: point Norm Sq column
-- statement:
--   The PT construction uses the point Norm Sq column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SupRatioLeOfPhaseZero.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SupRatioLeOfPhaseZero.lean#L49-L51

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
open ReciprocityTheory.ChartRestriction.G.I2.PT
variable (X : PT E)

theorem ReciprocityTheory.ChartRestriction.G.I2.PT.pointNormSq_column (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Vsp X.dim) :
    X.ptN2 1 s (fun _ => a) = X.toGT.ptN2 1 (X.col1 s) a := by sorry
