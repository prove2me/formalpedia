-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_int_comb_c953859cc094
-- name    : P2M_GroundTheory_Heights__Heights_exists_int_comb_c953859cc094
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:20.128631+00:00
-- url     : https://prove2.me/theorems/1f734607-63b2-4fa7-9f87-3eea7f16843a
-- title:
--   P2 M Ground Theory Heights  Heights exists int comb c953859cc094: P2 M Ground Theory Heights  Heights exists int comb c953859cc094
-- statement:
--   The P2 M Ground Theory Heights  Heights exists int comb c953859cc094 construction uses the P2 M Ground Theory Heights  Heights exists int comb c953859cc094 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L43-L49

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

theorem P2M_GroundTheory_Heights__Heights_exists_int_comb_c953859cc094 {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (v : Fin (r + 1) → K) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ c : Fin (N + 1) → ℤ, ∑ b, c b • φ b = D • v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_int_comb» := P2M_GroundTheory_Heights__Heights_exists_int_comb_c953859cc094
