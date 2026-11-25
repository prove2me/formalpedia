-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticePoint_mem_5d2a33e3dc3b
-- name    : P2M_GroundTheory_Heights__Heights_latticePoint_mem_5d2a33e3dc3b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:16.168328+00:00
-- url     : https://prove2.me/theorems/736cbe0f-da8d-4841-ace1-dc8b129e3b82
-- title:
--   P2 M Ground Theory Heights  Heights lattice Point mem 5d2a33e3dc3b: P2 M Ground Theory Heights  Heights lattice Point mem 5d2a33e3dc3b
-- statement:
--   The P2 M Ground Theory Heights  Heights lattice Point mem 5d2a33e3dc3b construction uses the P2 M Ground Theory Heights  Heights lattice Point mem 5d2a33e3dc3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L83-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L83-L95

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

theorem P2M_GroundTheory_Heights__Heights_latticePoint_mem_5d2a33e3dc3b {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (σ : K →+* ℂ) {w : Fin (r + 1) → ℂ} (hw : w ≠ 0) :
    latticePoint φ σ w ∈ conePoints (latticeIdeal φ) ℂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«latticePoint_mem» := P2M_GroundTheory_Heights__Heights_latticePoint_mem_5d2a33e3dc3b
