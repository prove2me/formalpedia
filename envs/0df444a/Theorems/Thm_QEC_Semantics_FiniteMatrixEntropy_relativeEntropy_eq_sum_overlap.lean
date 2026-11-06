-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_relativeEntropy_eq_sum_overlap
-- name    : QEC.Semantics.FiniteMatrixEntropy.relativeEntropy_eq_sum_overlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:18.882054+00:00
-- url     : https://prove2.me/theorems/a8cc0dbf-b6ff-4f7e-8473-05c7a93b70f6
-- title:
--   Finite Matrix Entropy: relative Entropy eq sum overlap
-- statement:
--   Relative entropy is the scalar Klein expression averaged over eigenbasis overlaps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L322-L344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L322-L344

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy

theorem QEC.Semantics.FiniteMatrixEntropy.relativeEntropy_eq_sum_overlap {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n Complex) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    relativeEntropy A B hA hB =
      ∑ i, ∑ j,
        overlapWeight hA.eigenvectorUnitary hB.eigenvectorUnitary i j *
          (hA.eigenvalues i *
            (Real.log (hA.eigenvalues i) - Real.log (hB.eigenvalues j))) := by sorry
