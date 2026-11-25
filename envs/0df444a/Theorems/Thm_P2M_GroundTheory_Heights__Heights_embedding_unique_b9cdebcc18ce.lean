-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_embedding_unique_b9cdebcc18ce
-- name    : P2M_GroundTheory_Heights__Heights_embedding_unique_b9cdebcc18ce
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:49:52.05599+00:00
-- url     : https://prove2.me/theorems/382ed75c-5de4-5f24-bc7b-4c5cab2ff471
-- title:
--   P2 M Ground Theory Heights  Heights embedding unique b9cdebcc18ce: P2 M Ground Theory Heights  Heights embedding unique b9cdebcc18ce
-- statement:
--   The P2 M Ground Theory Heights  Heights embedding unique b9cdebcc18ce construction uses the P2 M Ground Theory Heights  Heights embedding unique b9cdebcc18ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L97-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L97-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
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
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_embedding_unique_b9cdebcc18ce {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) {σ σ' : K →+* ℂ} {w w' : Fin (r + 1) → ℂ} (hw : w ≠ 0)
    (h : latticePoint φ σ w = latticePoint φ σ' w') : σ = σ' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«embedding_unique» := P2M_GroundTheory_Heights__Heights_embedding_unique_b9cdebcc18ce
