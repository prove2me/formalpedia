-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticePoint_ne_zero_40cbc107ef6e
-- name    : P2M_GroundTheory_Heights__Heights_latticePoint_ne_zero_40cbc107ef6e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:53.623799+00:00
-- url     : https://prove2.me/theorems/62cbeda1-63ef-4964-b62d-927ac10d2caa
-- title:
--   P2 M Ground Theory Heights  Heights lattice Point ne zero 40cbc107ef6e: P2 M Ground Theory Heights  Heights lattice Point ne zero 40cbc107ef6e
-- statement:
--   The P2 M Ground Theory Heights  Heights lattice Point ne zero 40cbc107ef6e construction uses the P2 M Ground Theory Heights  Heights lattice Point ne zero 40cbc107ef6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L70-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L70-L81

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

theorem P2M_GroundTheory_Heights__Heights_latticePoint_ne_zero_40cbc107ef6e {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (σ : K →+* ℂ) {w : Fin (r + 1) → ℂ} (hw : w ≠ 0) :
    latticePoint φ σ w () ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«latticePoint_ne_zero» := P2M_GroundTheory_Heights__Heights_latticePoint_ne_zero_40cbc107ef6e
