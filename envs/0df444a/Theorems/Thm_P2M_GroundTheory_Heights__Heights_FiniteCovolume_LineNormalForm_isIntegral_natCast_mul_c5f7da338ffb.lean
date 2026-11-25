-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_isIntegral_natCast_mul_c5f7da338ffb
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_isIntegral_natCast_mul_c5f7da338ffb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:56.332517+00:00
-- url     : https://prove2.me/theorems/c30427f4-a16b-410a-b636-9981d4115acd
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form is Integral nat Cast mul c5f7da338ffb: P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form is Integral nat Cast mu
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form is Integral nat Cast mul c5f7da338ffb construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form is Integral nat Cast mul c5f7da338ffb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L22-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIdealClassesFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineCoeffsFG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsCommonMultiple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineNormalForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.LineNormalForm
variable {E : Type*} [Field E] [NumberField E]
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_isIntegral_natCast_mul_c5f7da338ffb {n : ℕ} {x : E} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ ((n : E) * x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«LineNormalForm».«isIntegral_natCast_mul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_isIntegral_natCast_mul_c5f7da338ffb
