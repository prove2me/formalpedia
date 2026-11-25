-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_exists_smulSub_le_b0a4c2df638b
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_exists_smulSub_le_b0a4c2df638b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:57.194027+00:00
-- url     : https://prove2.me/theorems/73e9899e-0195-4e08-a00a-82a95eadce0b
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas exists smul Sub le b0a4c2df638b: P2 M Ground Theory Heights  Heights Lattice Lemmas exists smul Sub le b0a4c2df638b
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas exists smul Sub le b0a4c2df638b construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas exists smul Sub le b0a4c2df638b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L88-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L88-L98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
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
open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_exists_smulSub_le_b0a4c2df638b (M₁ M₂ : FullLattice K V) :
    ∃ b : 𝓞 K, b ≠ 0 ∧ smulSub b M₂.carrier ≤ M₁.carrier := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«exists_smulSub_le» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_exists_smulSub_le_b0a4c2df638b
