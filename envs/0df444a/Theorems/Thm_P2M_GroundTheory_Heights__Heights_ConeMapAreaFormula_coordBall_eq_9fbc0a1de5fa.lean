-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_coordBall_eq_9fbc0a1de5fa
-- name    : P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_coordBall_eq_9fbc0a1de5fa
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:58.385402+00:00
-- url     : https://prove2.me/theorems/e4f0f11e-dadc-5a66-9351-88410bebec6d
-- title:
--   P2 M Ground Theory Heights  Heights Cone Map Area Formula coord Ball eq 9fbc0a1de5fa: P2 M Ground Theory Heights  Heights Cone Map Area Formula coord Ball eq 9fbc0a1de5fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Map Area Formula coord Ball eq 9fbc0a1de5fa construction uses the P2 M Ground Theory Heights  Heights Cone Map Area Formula coord Ball eq 9fbc0a1de5fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L237-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L237-L263

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

theorem P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_coordBall_eq_9fbc0a1de5fa (m k : ℕ) :
    {y : EuclideanSpace ℂ (Fin (m + k)) | ‖y‖ < 1 ∧ ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0} =
      zeroExt m k '' Metric.ball 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMapAreaFormula».«coordBall_eq» := P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_coordBall_eq_9fbc0a1de5fa
