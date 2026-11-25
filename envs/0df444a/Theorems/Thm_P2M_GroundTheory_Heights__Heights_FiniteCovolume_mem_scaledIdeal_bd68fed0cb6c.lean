-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_scaledIdeal_bd68fed0cb6c
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_scaledIdeal_bd68fed0cb6c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:40:16.098868+00:00
-- url     : https://prove2.me/theorems/a2b4c37e-314d-4ed7-a86f-e78fd4875cec
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume mem scaled Ideal bd68fed0cb6c: P2 M Ground Theory Heights  Heights Finite Covolume mem scaled Ideal bd68fed0cb6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume mem scaled Ideal bd68fed0cb6c construction uses the P2 M Ground Theory Heights  Heights Finite Covolume mem scaled Ideal bd68fed0cb6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIdealClassesFinite.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIdealClassesFinite.lean#L31-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIdealClassesFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField
variable {E : Type*} [Field E] [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_scaledIdeal_bd68fed0cb6c {I : AddSubgroup E} {hI : ∀ a : 𝓞 E, ∀ x ∈ I, (a : E) * x ∈ I} {b : E}
    {y : 𝓞 E} : y ∈ scaledIdeal I hI b ↔ b⁻¹ * (y : E) ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«mem_scaledIdeal» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_scaledIdeal_bd68fed0cb6c
