-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_DensityOperator_vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix
-- name    : QEC.Semantics.FiniteMatrixEntropy.DensityOperator.vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:50:05.292592+00:00
-- url     : https://prove2.me/theorems/f3fd5b98-0b21-4be8-87fe-78619a2b94c3
-- title:
--   Density Operator: von Neumann Entropy eq neg real Trace mul log2 Matrix
-- statement:
--   The base-two entropy of #409 is the negative real trace pairing with `log2Matrix`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L799-L818
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L799-L818

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

theorem QEC.Semantics.FiniteMatrixEntropy.DensityOperator.vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (rho : DensityOperator H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    rho.vonNeumannEntropy =
      -realTrace (rho.spectralMatrix b * log2Matrix (rho.spectralMatrix b)
        (rho.spectralMatrix_isHermitian b)) := by sorry
