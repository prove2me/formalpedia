-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagStaircaseOrbit_bijective_of_injective_5dfb25d50c40
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagStaircaseOrbit_bijective_of_injective_5dfb25d50c40
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:19:47.841004+00:00
-- url     : https://prove2.me/theorems/66d58886-57d4-453c-9d20-51f7ffeff3f5
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Staircase Orbit bijective of injective 5dfb25d50c40: P2 M Ground Theory Heights  Heights Rest Terms Flag Staircase Orbit bijective of injective 5dfb
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Staircase Orbit bijective of injective 5dfb25d50c40 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Staircase Orbit bijective of injective 5dfb25d50c40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagStaircaseOrbit.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagStaircaseOrbit.lean#L9-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagStaircaseOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagStaircaseOrbit_bijective_of_injective_5dfb25d50c40 {f N : ℕ} (γ : Fin f × Fin N →₀ ℕ) (τ : Fin f)
    (hlt : ∀ i, γ (τ, i) < N) (hinj : Function.Injective fun i : Fin N => γ (τ, i)) :
    Function.Bijective fun i : Fin N => (⟨γ (τ, i), hlt i⟩ : Fin N) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagStaircaseOrbit».«bijective_of_injective» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagStaircaseOrbit_bijective_of_injective_5dfb25d50c40
