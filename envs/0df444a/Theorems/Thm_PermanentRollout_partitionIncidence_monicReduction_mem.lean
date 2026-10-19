-- Prove2me | Theorems.Thm_PermanentRollout_partitionIncidence_monicReduction_mem
-- name    : PermanentRollout.partitionIncidence_monicReduction_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/d23b7149-76b7-42a5-8b8e-30a8468d04ae
-- title:
--   PermanentRollout.partitionIncidence_monicReduction_mem
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.partitionIncidence_monicReduction_mem
    (t s d : ℕ) (column : Fin s) (i : Fin t) :
    let q := d - 1
    let k : ℂ := ((t - q : ℕ) : ℂ)
    let a : ℂ := (-1 : ℂ) ^ q * (q.factorial : ℂ)
    let embed : Fin t → IncidenceCoordinate t s :=
      fun row => Sum.inr (column, row)
    let D : Fin t → MvPolynomial (IncidenceCoordinate t s) ℂ :=
      fun row => MvPolynomial.rename embed
        (deletedCoordinateEsymmPolynomial t q row)
    let E : ℕ → MvPolynomial (IncidenceCoordinate t s) ℂ :=
      fun j => MvPolynomial.rename embed
        (partitionFiberCoordinateEsymmPolynomial t j)
    let R : Fin t → MvPolynomial (IncidenceCoordinate t s) ℂ :=
      fun row => partitionIncidenceEquation t s d column row -
        MvPolynomial.C a * D row
    MvPolynomial.C k *
        (MvPolynomial.C a *
          (∑ j ∈ Finset.range q,
            (-MvPolynomial.X (Sum.inr (column, i))) ^ (q - j) * E j) +
          R i) -
        ∑ row : Fin t, R row ∈ partitionIncidenceIdeal t s d := by sorry
