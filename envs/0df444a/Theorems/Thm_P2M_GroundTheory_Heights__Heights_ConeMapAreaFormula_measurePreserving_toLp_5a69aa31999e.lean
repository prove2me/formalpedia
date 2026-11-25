-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_measurePreserving_toLp_5a69aa31999e
-- name    : P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_measurePreserving_toLp_5a69aa31999e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:01.424015+00:00
-- url     : https://prove2.me/theorems/14345876-c0e8-4d7e-a1ac-a85579f48c4f
-- title:
--   P2 M Ground Theory Heights  Heights Cone Map Area Formula measure Preserving to Lp 5a69aa31999e: P2 M Ground Theory Heights  Heights Cone Map Area Formula measure Preserving to Lp 5a69aa31999e
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Map Area Formula measure Preserving to Lp 5a69aa31999e construction uses the P2 M Ground Theory Heights  Heights Cone Map Area Formula measure Preserving to Lp 5a69aa31999e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L58-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L58-L75

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

theorem P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_measurePreserving_toLp_5a69aa31999e (m : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : (Fin m → ℂ) → EuclideanSpace ℂ (Fin m)) volume volume := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMapAreaFormula».«measurePreserving_toLp» := P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_measurePreserving_toLp_5a69aa31999e
