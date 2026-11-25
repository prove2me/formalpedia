-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_volume_ball_E_03894f69c9b1
-- name    : P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_volume_ball_E_03894f69c9b1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:54.378353+00:00
-- url     : https://prove2.me/theorems/06738a6c-8884-4c7c-9eb8-485b70fd0f3b
-- title:
--   P2 M Ground Theory Heights  Heights Cone Map Area Formula volume ball E 03894f69c9b1: P2 M Ground Theory Heights  Heights Cone Map Area Formula volume ball E 03894f69c9b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Map Area Formula volume ball E 03894f69c9b1 construction uses the P2 M Ground Theory Heights  Heights Cone Map Area Formula volume ball E 03894f69c9b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L230-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L230-L235

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

theorem P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_volume_ball_E_03894f69c9b1 (e : ℕ) :
    volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) =
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMapAreaFormula».«volume_ball_E» := P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_volume_ball_E_03894f69c9b1
