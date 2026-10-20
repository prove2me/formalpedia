-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_allRank_finSucc_exists_source_arbitraryPivotPlaneQuotient_induction
-- name    : PermanentRollout.homogeneousMap_allRank_finSucc_exists_source_arbitraryPivotPlaneQuotient_induction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:36.286012+00:00
-- url     : https://prove2.me/theorems/68c3daeb-47d0-42ba-b2ae-8353a14dd6c5
-- title:
--   PermanentRollout.homogeneousMap_allRank_finSucc_exists_source_arbitraryPivotPlaneQuotient_induction
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

theorem PermanentRollout.homogeneousMap_allRank_finSucc_exists_source_arbitraryPivotPlaneQuotient_induction
    {n : ℕ}
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin (n + 1) → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    ∃ (c : Fin (n + 1) → ℂ) (j : Fin (n + 1)) (hj : c j ≠ 0),
      (∀ i : Fin n,
        (homogeneousMapFinSuccArbitraryPivotPlaneQuotientEquiv c j hj
          (Ideal.Quotient.mk
            (Ideal.span
              ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
                Set (MvPolynomial (Fin (n + 1)) ℂ)))
            (F i.castSucc))).IsHomogeneous e) ∧
      (∀ u : Fin n → ℂ,
        (∀ i : Fin n,
          MvPolynomial.eval u
            (homogeneousMapFinSuccArbitraryPivotPlaneQuotientEquiv c j hj
              (Ideal.Quotient.mk
                (Ideal.span
                  ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
                    Set (MvPolynomial (Fin (n + 1)) ℂ)))
                (F i.castSucc))) = 0) ↔ u = 0) := by sorry
