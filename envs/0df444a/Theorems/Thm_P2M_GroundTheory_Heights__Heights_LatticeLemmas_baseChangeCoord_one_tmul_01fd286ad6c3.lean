-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_baseChangeCoord_one_tmul_01fd286ad6c3
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_baseChangeCoord_one_tmul_01fd286ad6c3
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:20.797954+00:00
-- url     : https://prove2.me/theorems/52fe6365-ed5b-46b3-987e-21685177e23c
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas base Change Coord one tmul 01fd286ad6c3: P2 M Ground Theory Heights  Heights Lattice Lemmas base Change Coord one tmul 01fd286ad6c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas base Change Coord one tmul 01fd286ad6c3 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas base Change Coord one tmul 01fd286ad6c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PBaseChange.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PBaseChange.lean#L20-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_BaseChangeIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField TensorProduct ComplexAt GroundTheory.Heights₂.Heights
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]
omit [NumberField K] [NumberField L] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_baseChangeCoord_one_tmul_01fd286ad6c3 (τ : L →+* ℂ) (e : E) :
    baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] e)) =
      (1 : ComplexAt (τ.comp (algebraMap K L))) ⊗ₜ e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«baseChangeCoord_one_tmul» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_baseChangeCoord_one_tmul_01fd286ad6c3
