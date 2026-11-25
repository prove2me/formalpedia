-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_volume_preserving_uncurry_665ed32e1d59
-- name    : P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_volume_preserving_uncurry_665ed32e1d59
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:45.525848+00:00
-- url     : https://prove2.me/theorems/3032ca3c-3862-41c6-8349-0bfb45904b2f
-- title:
--   P2 M Ground Theory Heights  Heights Cone Map Area Formula volume preserving uncurry 665ed32e1d59: P2 M Ground Theory Heights  Heights Cone Map Area Formula volume preserving uncurry 665ed32e1d59
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Map Area Formula volume preserving uncurry 665ed32e1d59 construction uses the P2 M Ground Theory Heights  Heights Cone Map Area Formula volume preserving uncurry 665ed32e1d59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L54-L56

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

theorem P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_volume_preserving_uncurry_665ed32e1d59 (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (Function.uncurry : (ι → κ → ℝ) → ι × κ → ℝ) volume volume := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMapAreaFormula».«volume_preserving_uncurry» := P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_volume_preserving_uncurry_665ed32e1d59
