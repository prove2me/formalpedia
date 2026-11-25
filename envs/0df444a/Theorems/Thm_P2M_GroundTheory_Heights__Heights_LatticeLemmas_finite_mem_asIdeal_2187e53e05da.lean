-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_finite_mem_asIdeal_2187e53e05da
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_finite_mem_asIdeal_2187e53e05da
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:22.286955+00:00
-- url     : https://prove2.me/theorems/e44cb465-6abe-5c5f-9e36-f4e82613d3ea
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas finite mem as Ideal 2187e53e05da: P2 M Ground Theory Heights  Heights Lattice Lemmas finite mem as Ideal 2187e53e05da
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas finite mem as Ideal 2187e53e05da construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas finite mem as Ideal 2187e53e05da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L138-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L138-L146

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

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_finite_mem_asIdeal_2187e53e05da {b : 𝓞 K} (hb : b ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | b ∈ v.asIdeal}.Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«finite_mem_asIdeal» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_finite_mem_asIdeal_2187e53e05da
