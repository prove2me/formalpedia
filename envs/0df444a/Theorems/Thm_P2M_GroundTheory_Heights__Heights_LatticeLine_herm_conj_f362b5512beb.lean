-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLine_herm_conj_f362b5512beb
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLine_herm_conj_f362b5512beb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:35.477316+00:00
-- url     : https://prove2.me/theorems/f72aa028-7bc8-4ef0-aea8-e3c9eb640585
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Line herm conj f362b5512beb: P2 M Ground Theory Heights  Heights Lattice Line herm conj f362b5512beb
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Line herm conj f362b5512beb construction uses the P2 M Ground Theory Heights  Heights Lattice Line herm conj f362b5512beb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLatticeLineExists.lean#L141-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLatticeLineExists.lean#L141-L149

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLatticeLineExists
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
open NumberField Matrix
open scoped ComplexOrder ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LatticeLine
variable {K : Type} [Field K] [NumberField K] {r N : ℕ}
variable (F : HermLattice K (r + 1)) (φ : Fin (N + 1) → Fin (r + 1) → K)
  (R : (K →+* ℂ) → Fin (r + 1) → Fin (N + 1) → ℂ)

theorem P2M_GroundTheory_Heights__Heights_LatticeLine_herm_conj_f362b5512beb (s : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    (star (fun j ↦ starRingEnd ℂ (w j)) ⬝ᵥ
        (F.metric (ComplexEmbedding.conjugate s) *ᵥ fun j ↦ starRingEnd ℂ (w j))).re =
      (star w ⬝ᵥ (F.metric s *ᵥ w)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLine».«herm_conj» := P2M_GroundTheory_Heights__Heights_LatticeLine_herm_conj_f362b5512beb
