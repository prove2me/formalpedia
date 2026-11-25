-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_star_dotProduct_mulVec_of_isHermitian_f0205efbd7ec
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_star_dotProduct_mulVec_of_isHermitian_f0205efbd7ec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:39:31.975195+00:00
-- url     : https://prove2.me/theorems/0832f318-a04d-5abd-ab4d-81de121e23d6
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume star dot Product mul Vec of is Hermitian f0205efbd7ec: P2 M Ground Theory Heights  Heights Finite Covolume star dot Product mul Vec of is Hermitian
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume star dot Product mul Vec of is Hermitian f0205efbd7ec construction uses the P2 M Ground Theory Heights  Heights Finite Covolume star dot Product mul Vec of is Hermitian f0205efbd7ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PEigenReflectionMaps.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PEigenReflectionMaps.lean#L15-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PEigenReflectionMaps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
open scoped ComplexOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_star_dotProduct_mulVec_of_isHermitian_f0205efbd7ec {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (x y : ι → ℂ) : star (star y ⬝ᵥ (P *ᵥ x)) = star x ⬝ᵥ (P *ᵥ y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«star_dotProduct_mulVec_of_isHermitian» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_star_dotProduct_mulVec_of_isHermitian_f0205efbd7ec
