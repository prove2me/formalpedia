-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLine_conj_point_933b0adfa5ff
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLine_conj_point_933b0adfa5ff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:06.366041+00:00
-- url     : https://prove2.me/theorems/1e8a9e23-ca91-42f2-ab2c-eb6aef310215
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Line conj point 933b0adfa5ff: P2 M Ground Theory Heights  Heights Lattice Line conj point 933b0adfa5ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Line conj point 933b0adfa5ff construction uses the P2 M Ground Theory Heights  Heights Lattice Line conj point 933b0adfa5ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLatticeLineExists.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLatticeLineExists.lean#L135-L139

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

theorem P2M_GroundTheory_Heights__Heights_LatticeLine_conj_point_933b0adfa5ff (s : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    (fun b ↦ starRingEnd ℂ (latticePoint φ s w () b)) =
      latticePoint φ (ComplexEmbedding.conjugate s) (fun j ↦ starRingEnd ℂ (w j)) () := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLine».«conj_point» := P2M_GroundTheory_Heights__Heights_LatticeLine_conj_point_933b0adfa5ff
