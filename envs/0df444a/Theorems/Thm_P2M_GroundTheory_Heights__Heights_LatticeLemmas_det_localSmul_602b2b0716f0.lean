-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_det_localSmul_602b2b0716f0
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_det_localSmul_602b2b0716f0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:40:03.70091+00:00
-- url     : https://prove2.me/theorems/26a0483e-07c8-4113-a8cc-b75551f3de61
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas det local Smul 602b2b0716f0: P2 M Ground Theory Heights  Heights Lattice Lemmas det local Smul 602b2b0716f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas det local Smul 602b2b0716f0 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas det local Smul 602b2b0716f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L124-L131

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
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_det_localSmul_602b2b0716f0 (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} (hb : b ≠ 0) :
    LinearMap.det ((localSmul v hb : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] _) :
      (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) =
      localScalar v b ^ Module.finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] V) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«det_localSmul» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_det_localSmul_602b2b0716f0
