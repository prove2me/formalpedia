-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_hausdorff_eq_zero_of_lt_3901e9dd64fb
-- name    : P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_hausdorff_eq_zero_of_lt_3901e9dd64fb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:10.096345+00:00
-- url     : https://prove2.me/theorems/6e088f23-610e-546a-b751-f4024693f64d
-- title:
--   P2 M Ground Theory Heights  Heights Cone Map Area Formula hausdorff eq zero of lt 3901e9dd64fb: P2 M Ground Theory Heights  Heights Cone Map Area Formula hausdorff eq zero of lt 3901e9dd64fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Map Area Formula hausdorff eq zero of lt 3901e9dd64fb construction uses the P2 M Ground Theory Heights  Heights Cone Map Area Formula hausdorff eq zero of lt 3901e9dd64fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L221-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L221-L228

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapAreaOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VolumePreservingUncurry
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMapAreaOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal NNReal ComplexOrder
open GroundTheory.Heights₂.Heights.ConeMapAreaFormula

theorem P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_hausdorff_eq_zero_of_lt_3901e9dd64fb {n d : ℕ} (h : n < d) :
    (Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) : Measure (EuclideanSpace ℂ (Fin n))) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMapAreaFormula».«hausdorff_eq_zero_of_lt» := P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_hausdorff_eq_zero_of_lt_3901e9dd64fb
