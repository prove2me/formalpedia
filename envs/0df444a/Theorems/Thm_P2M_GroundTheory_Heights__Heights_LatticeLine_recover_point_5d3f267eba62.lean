-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLine_recover_point_5d3f267eba62
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLine_recover_point_5d3f267eba62
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:36.361453+00:00
-- url     : https://prove2.me/theorems/921d1607-e288-4392-abaf-4cf81f370b78
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Line recover point 5d3f267eba62: P2 M Ground Theory Heights  Heights Lattice Line recover point 5d3f267eba62
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Line recover point 5d3f267eba62 construction uses the P2 M Ground Theory Heights  Heights Lattice Line recover point 5d3f267eba62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLatticeLineExists.lean#L99-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLatticeLineExists.lean#L99-L115

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
omit [NumberField K]
open Classical

theorem P2M_GroundTheory_Heights__Heights_LatticeLine_recover_point_5d3f267eba62
    (hR : ∀ (σ : K →+* ℂ) (j₀ : Fin (r + 1)) (τ : K →+* ℂ) (j : Fin (r + 1)),
      ∑ b, R σ j₀ b * τ (φ b j) = if τ = σ ∧ j = j₀ then 1 else 0)
    (s t : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    recover R t (latticePoint φ s w ()) = if t = s then w else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLine».«recover_point» := P2M_GroundTheory_Heights__Heights_LatticeLine_recover_point_5d3f267eba62
