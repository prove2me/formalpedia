-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_congruenceUnits_f43d8290014c
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_congruenceUnits_f43d8290014c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:40:34.63885+00:00
-- url     : https://prove2.me/theorems/fae1a2e6-f639-4a6f-a08b-e66e8603ccb3
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume mem congruence Units f43d8290014c: P2 M Ground Theory Heights  Heights Finite Covolume mem congruence Units f43d8290014c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume mem congruence Units f43d8290014c construction uses the P2 M Ground Theory Heights  Heights Finite Covolume mem congruence Units f43d8290014c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsVectorOrbits.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsVectorOrbits.lean#L20-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits
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
open scoped Pointwise
noncomputable section
variable (E : Type*) [Field E] [NumberField E]
omit [NumberField E]
variable {E}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_congruenceUnits_f43d8290014c {N : ℕ} {ε : (𝓞 E)ˣ} :
    ε ∈ congruenceUnits E N ↔ (ε : 𝓞 E) - 1 ∈ Ideal.span {(N : 𝓞 E)} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«mem_congruenceUnits» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_congruenceUnits_f43d8290014c
