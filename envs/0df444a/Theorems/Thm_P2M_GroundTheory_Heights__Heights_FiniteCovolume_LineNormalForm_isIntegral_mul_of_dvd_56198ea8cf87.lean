-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_isIntegral_mul_of_dvd_56198ea8cf87
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_isIntegral_mul_of_dvd_56198ea8cf87
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:29:25.619153+00:00
-- url     : https://prove2.me/theorems/d1a5e5d5-1530-5f3f-96be-c43e90e4a4c9
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form is Integral mul of dvd 56198ea8cf87: P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form is Integral mul of dvd 56
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form is Integral mul of dvd 56198ea8cf87 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form is Integral mul of dvd 56198ea8cf87 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L30-L35

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_isIntegral_mul_of_dvd_56198ea8cf87 {a b : ℕ} {x : E} (hx : IsIntegral ℤ ((a : E) * x)) (hab : a ∣ b) :
    IsIntegral ℤ ((b : E) * x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«LineNormalForm».«isIntegral_mul_of_dvd» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_isIntegral_mul_of_dvd_56198ea8cf87
