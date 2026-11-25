-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_nat_mul_isIntegral_0b76cb35c68e
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_nat_mul_isIntegral_0b76cb35c68e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:32:18.242794+00:00
-- url     : https://prove2.me/theorems/bffc01db-c327-41d4-be3c-a4d8014ba756
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form exists nat mul is Integral 0b76cb35c68e: P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form exists nat mul is Int
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form exists nat mul is Integral 0b76cb35c68e construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form exists nat mul is Integral 0b76cb35c68e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L37-L48

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_nat_mul_isIntegral_0b76cb35c68e (x : E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«LineNormalForm».«exists_nat_mul_isIntegral» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_nat_mul_isIntegral_0b76cb35c68e
