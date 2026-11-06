-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_epsilon_regularized_relativeEntropy_nonnegative
-- name    : QEC.Semantics.FiniteMatrixEntropy.epsilon_regularized_relativeEntropy_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:49:25.04434+00:00
-- url     : https://prove2.me/theorems/178c62a1-d537-4ed9-9308-c2c4f540305a
-- title:
--   Finite Matrix Entropy: epsilon regularized relative Entropy nonnegative
-- statement:
--   Epsilon-regularized relative entropy is nonnegative for arbitrary finite
--   trace-one positive semidefinite matrices, including singular inputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L459-L476
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L459-L476

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

theorem QEC.Semantics.FiniteMatrixEntropy.epsilon_regularized_relativeEntropy_nonnegative
    {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n Complex) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAtrace : realTrace A = 1) (hBtrace : realTrace B = 1)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    0 <= relativeEntropy A (epsilonRegularize B epsilon) hA.isHermitian
      (epsilonRegularize_posDef B hB hepsilon).isHermitian := by sorry
