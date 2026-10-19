-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMapFinSucc_exists_source_arbitraryPivot_restricted_zeroFiber
-- name    : PermanentRollout.homogeneousMapFinSucc_exists_source_arbitraryPivot_restricted_zeroFiber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/a6b6178e-ba9e-4ece-9511-6cdd68d2ffeb
-- title:
--   PermanentRollout.homogeneousMapFinSucc_exists_source_arbitraryPivot_restricted_zeroFiber
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

theorem PermanentRollout.homogeneousMapFinSucc_exists_source_arbitraryPivot_restricted_zeroFiber
    {n : ℕ}
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin (n + 1) → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    ∃ (c : Fin (n + 1) → ℂ) (j : Fin (n + 1)),
      c j ≠ 0 ∧
      (∀ i : Fin n,
        (MvPolynomial.aeval
          (fun row => linearCoordinatePolynomial
            (homogeneousMapFinSuccArbitraryPivotPlaneMap c j) row)
          (F i.castSucc)).IsHomogeneous e) ∧
      (∀ u : Fin n → ℂ,
        (∀ i : Fin n,
          MvPolynomial.eval u
            (MvPolynomial.aeval
              (fun row => linearCoordinatePolynomial
                (homogeneousMapFinSuccArbitraryPivotPlaneMap c j) row)
              (F i.castSucc)) = 0) ↔ u = 0) := by sorry
