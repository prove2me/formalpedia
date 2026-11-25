-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_localLattice_baseChange_37285dfb9883
-- name    : P2M_GroundTheory_Heights__Heights_localLattice_baseChange_37285dfb9883
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:59.805385+00:00
-- url     : https://prove2.me/theorems/fb4e9f66-a1f4-4728-bdc1-67cb0d86de33
-- title:
--   P2 M Ground Theory Heights  Heights local Lattice base Change 37285dfb9883: P2 M Ground Theory Heights  Heights local Lattice base Change 37285dfb9883
-- statement:
--   The P2 M Ground Theory Heights  Heights local Lattice base Change 37285dfb9883 construction uses the P2 M Ground Theory Heights  Heights local Lattice base Change 37285dfb9883 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L169-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L169-L183

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (v : HeightOneSpectrum (𝓞 K))

theorem P2M_GroundTheory_Heights__Heights_localLattice_baseChange_37285dfb9883 (e : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V)
    (he : L.map (e.toLinearMap.restrictScalars (𝓞 K)) = L) :
    (localLattice v L : Set (v.adicCompletion K ⊗[K] V)) =
      e.baseChange K (v.adicCompletion K) V V '' localLattice v L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«localLattice_baseChange» := P2M_GroundTheory_Heights__Heights_localLattice_baseChange_37285dfb9883
