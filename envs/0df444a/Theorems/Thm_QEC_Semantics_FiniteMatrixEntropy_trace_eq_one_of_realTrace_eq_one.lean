-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_trace_eq_one_of_realTrace_eq_one
-- name    : QEC.Semantics.FiniteMatrixEntropy.trace_eq_one_of_realTrace_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:18:29.059076+00:00
-- url     : https://prove2.me/theorems/2ac94257-d5f9-4730-9192-38b3476558e7
-- title:
--   Finite Matrix Entropy: trace eq one of real Trace eq one
-- statement:
--   A Hermitian trace-one matrix has complex trace equal to one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L468-L475
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L468-L475

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy

theorem QEC.Semantics.FiniteMatrixEntropy.trace_eq_one_of_realTrace_eq_one
    {n : Type v} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.PosSemidef) (hBtrace : realTrace B = 1) :
    B.trace = 1 := by sorry
