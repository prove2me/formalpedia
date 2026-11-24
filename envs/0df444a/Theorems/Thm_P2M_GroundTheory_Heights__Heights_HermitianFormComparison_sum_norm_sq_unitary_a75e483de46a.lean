-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianFormComparison_sum_norm_sq_unitary_a75e483de46a
-- name    : P2M_GroundTheory_Heights__Heights_HermitianFormComparison_sum_norm_sq_unitary_a75e483de46a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:55.689563+00:00
-- url     : https://prove2.me/theorems/484323f5-a296-40f8-ace8-a5cb13a1af3c
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Form Comparison sum norm sq unitary a75e483de46a: P2 M Ground Theory Heights  Heights Hermitian Form Comparison sum norm sq unitary a75e483de46a
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Form Comparison sum norm sq unitary a75e483de46a construction uses the P2 M Ground Theory Heights  Heights Hermitian Form Comparison sum norm sq unitary a75e483de46a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHermFormCompare.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHermFormCompare.lean#L12-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
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
open Matrix
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.HermitianFormComparison

theorem P2M_GroundTheory_Heights__Heights_HermitianFormComparison_sum_norm_sq_unitary_a75e483de46a {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * star U = 1)
    (x : Fin n → ℂ) : ∑ k, ‖(star U *ᵥ x) k‖ ^ 2 = (star x ⬝ᵥ x).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianFormComparison».«sum_norm_sq_unitary» := P2M_GroundTheory_Heights__Heights_HermitianFormComparison_sum_norm_sq_unitary_a75e483de46a
