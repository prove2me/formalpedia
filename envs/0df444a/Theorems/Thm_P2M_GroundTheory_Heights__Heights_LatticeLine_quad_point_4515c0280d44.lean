-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLine_quad_point_4515c0280d44
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLine_quad_point_4515c0280d44
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:25.789415+00:00
-- url     : https://prove2.me/theorems/0093577d-3457-435b-bebb-164d139e456e
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Line quad point 4515c0280d44: P2 M Ground Theory Heights  Heights Lattice Line quad point 4515c0280d44
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Line quad point 4515c0280d44 construction uses the P2 M Ground Theory Heights  Heights Lattice Line quad point 4515c0280d44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLatticeLineExists.lean#L119-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLatticeLineExists.lean#L119-L131

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_LatticeLine_quad_point_4515c0280d44
    (hR : ∀ (σ : K →+* ℂ) (j₀ : Fin (r + 1)) (τ : K →+* ℂ) (j : Fin (r + 1)),
      ∑ b, R σ j₀ b * τ (φ b j) = if τ = σ ∧ j = j₀ then 1 else 0)
    (s : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    quad F φ R (latticePoint φ s w ()) = (star w ⬝ᵥ (F.metric s *ᵥ w)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLine».«quad_point» := P2M_GroundTheory_Heights__Heights_LatticeLine_quad_point_4515c0280d44
