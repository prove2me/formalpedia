-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_den_of_fg_b9c8a444fbec
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_den_of_fg_b9c8a444fbec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:35:45.390622+00:00
-- url     : https://prove2.me/theorems/96d9213f-3a47-5966-bbe5-2a4444094a2a
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form exists den of fg b9c8a444fbec: P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form exists den of fg b9c8a444fbec
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form exists den of fg b9c8a444fbec construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form exists den of fg b9c8a444fbec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L57-L67

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_den_of_fg_b9c8a444fbec {J : AddSubgroup E} (hJ : J.FG) :
    ∃ d : ℕ, 0 < d ∧ ∀ j ∈ J, IsIntegral ℤ ((d : E) * j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«LineNormalForm».«exists_den_of_fg» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_den_of_fg_b9c8a444fbec
