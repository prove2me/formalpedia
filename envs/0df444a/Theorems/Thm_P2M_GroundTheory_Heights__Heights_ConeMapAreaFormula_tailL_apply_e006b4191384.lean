-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_tailL_apply_e006b4191384
-- name    : P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_tailL_apply_e006b4191384
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:28.505345+00:00
-- url     : https://prove2.me/theorems/9c5ffabc-aa0f-4bd1-9acd-9bab5c497a6b
-- title:
--   P2 M Ground Theory Heights  Heights Cone Map Area Formula tail L apply e006b4191384: P2 M Ground Theory Heights  Heights Cone Map Area Formula tail L apply e006b4191384
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Map Area Formula tail L apply e006b4191384 construction uses the P2 M Ground Theory Heights  Heights Cone Map Area Formula tail L apply e006b4191384 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L95-L97

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

theorem P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_tailL_apply_e006b4191384 (e : ℕ) (p : EuclideanSpace ℂ (Fin (e + 1))) (j : Fin e) :
    tailL e p j = p j.succ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMapAreaFormula».«tailL_apply» := P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_tailL_apply_e006b4191384
