-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_latticePoint_eq_1f36b469e9bf
-- name    : P2M_GroundTheory_Heights__Heights_exists_latticePoint_eq_1f36b469e9bf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:47.624241+00:00
-- url     : https://prove2.me/theorems/d3626b79-7f01-4ab6-8ad7-19bd2b07fb19
-- title:
--   P2 M Ground Theory Heights  Heights exists lattice Point eq 1f36b469e9bf: P2 M Ground Theory Heights  Heights exists lattice Point eq 1f36b469e9bf
-- statement:
--   The P2 M Ground Theory Heights  Heights exists lattice Point eq 1f36b469e9bf construction uses the P2 M Ground Theory Heights  Heights exists lattice Point eq 1f36b469e9bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L184-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L184-L261

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

theorem P2M_GroundTheory_Heights__Heights_exists_latticePoint_eq_1f36b469e9bf {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) {z : Cone (fun _ : Unit ↦ N) ℂ}
    (hz : z ∈ conePoints (latticeIdeal φ) ℂ) :
    ∃ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 ∧ z = latticePoint φ σ w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_latticePoint_eq» := P2M_GroundTheory_Heights__Heights_exists_latticePoint_eq_1f36b469e9bf
