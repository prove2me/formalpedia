-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_allRank_finSucc_lastCoordinate_isSMulRegular_of_slice_weaklyRegular
-- name    : PermanentRollout.homogeneousMap_allRank_finSucc_lastCoordinate_isSMulRegular_of_slice_weaklyRegular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:36.286012+00:00
-- url     : https://prove2.me/theorems/7d6b227c-0cab-49e3-bc45-fc476e3cc495
-- title:
--   PermanentRollout.homogeneousMap_allRank_finSucc_lastCoordinate_isSMulRegular_of_slice_weaklyRegular
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
open scoped BigOperators

theorem PermanentRollout.homogeneousMap_allRank_finSucc_lastCoordinate_isSMulRegular_of_slice_weaklyRegular
    {n : ℕ}
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ)
    (hzero : ∀ point : Fin (n + 1) → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (c : Fin (n + 1) → ℂ)
    (j : Fin (n + 1)) (hj : c j ≠ 0)
    (hregular :
      RingTheory.Sequence.IsWeaklyRegular
        (MvPolynomial (Fin (n + 1)) ℂ ⧸
          Ideal.span
            ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
              Set (MvPolynomial (Fin (n + 1)) ℂ)))
        (List.ofFn fun i : Fin n =>
          Ideal.Quotient.mk
            (Ideal.span
              ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
                Set (MvPolynomial (Fin (n + 1)) ℂ)))
            (F i.castSucc))) :
    IsSMulRegular
      (MvPolynomial (Fin (n + 1)) ℂ ⧸
        Ideal.span (Set.range fun i : Fin n => F i.castSucc))
      (F (Fin.last n)) := by sorry
