-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_splitE_apply_152b7a9725df
-- name    : P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_splitE_apply_152b7a9725df
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:00.781417+00:00
-- url     : https://prove2.me/theorems/e687b4fa-8ee4-55fa-ae8a-9c670b76db2f
-- title:
--   P2 M Ground Theory Heights  Heights Cone Map Area Formula split E apply 152b7a9725df: P2 M Ground Theory Heights  Heights Cone Map Area Formula split E apply 152b7a9725df
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Map Area Formula split E apply 152b7a9725df construction uses the P2 M Ground Theory Heights  Heights Cone Map Area Formula split E apply 152b7a9725df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L81-L83

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

theorem P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_splitE_apply_152b7a9725df (e : ℕ) (p : EuclideanSpace ℂ (Fin (e + 1))) :
    splitE e p = (fun j => p j.succ, p 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMapAreaFormula».«splitE_apply» := P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_splitE_apply_152b7a9725df
