-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_norm_localScalar_eq_one_50c7d51bd0c9
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_norm_localScalar_eq_one_50c7d51bd0c9
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:38.111074+00:00
-- url     : https://prove2.me/theorems/70316ae2-d505-43c0-a193-6b8a567d96d9
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas norm local Scalar eq one 50c7d51bd0c9: P2 M Ground Theory Heights  Heights Lattice Lemmas norm local Scalar eq one 50c7d51bd0c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas norm local Scalar eq one 50c7d51bd0c9 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas norm local Scalar eq one 50c7d51bd0c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L133-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L133-L136

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

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_norm_localScalar_eq_one_50c7d51bd0c9 (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} (hv : b ∉ v.asIdeal) :
    ‖localScalar v b‖ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«norm_localScalar_eq_one» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_norm_localScalar_eq_one_50c7d51bd0c9
