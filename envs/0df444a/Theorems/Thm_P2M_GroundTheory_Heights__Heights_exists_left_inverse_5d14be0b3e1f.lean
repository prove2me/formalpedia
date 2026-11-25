-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_left_inverse_5d14be0b3e1f
-- name    : P2M_GroundTheory_Heights__Heights_exists_left_inverse_5d14be0b3e1f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:28.05068+00:00
-- url     : https://prove2.me/theorems/2cde7d7e-3e85-41ae-837e-a9b6ab5a1f6d
-- title:
--   P2 M Ground Theory Heights  Heights exists left inverse 5d14be0b3e1f: P2 M Ground Theory Heights  Heights exists left inverse 5d14be0b3e1f
-- statement:
--   The P2 M Ground Theory Heights  Heights exists left inverse 5d14be0b3e1f construction uses the P2 M Ground Theory Heights  Heights exists left inverse 5d14be0b3e1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L265-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L265-L329

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_exists_left_inverse_5d14be0b3e1f {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (σ : K →+* ℂ) (j₀ : Fin (r + 1)) :
    ∃ R : Fin (N + 1) → ℂ, ∀ (τ : K →+* ℂ) (j : Fin (r + 1)),
      ∑ b, R b * τ (φ b j) = if τ = σ ∧ j = j₀ then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_left_inverse» := P2M_GroundTheory_Heights__Heights_exists_left_inverse_5d14be0b3e1f
