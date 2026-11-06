-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_epsilonRegularize
-- name    : QEC.Semantics.FiniteMatrixEntropy.realTrace_epsilonRegularize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:39:07.497538+00:00
-- url     : https://prove2.me/theorems/9932bba3-d250-465c-b527-b4fe547fccab
-- title:
--   Finite Matrix Entropy: real Trace epsilon Regularize
-- statement:
--   Normalized epsilon regularization preserves the trace-one condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L437-L453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L437-L453

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

theorem QEC.Semantics.FiniteMatrixEntropy.realTrace_epsilonRegularize {n : Type u} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.PosSemidef) (hBtrace : realTrace B = 1)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    realTrace (epsilonRegularize B epsilon) = 1 := by sorry
