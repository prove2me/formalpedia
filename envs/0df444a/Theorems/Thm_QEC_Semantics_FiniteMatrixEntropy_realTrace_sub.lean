-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_sub
-- name    : QEC.Semantics.FiniteMatrixEntropy.realTrace_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:18:29.793461+00:00
-- url     : https://prove2.me/theorems/a0fdb08b-6e88-42e0-b387-34f3df005bf4
-- title:
--   Finite Matrix Entropy: real Trace sub
-- statement:
--   The real trace pairing preserves subtraction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L484-L487
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L484-L487

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

theorem QEC.Semantics.FiniteMatrixEntropy.realTrace_sub {n : Type v} [Fintype n]
    (A B : Matrix n n Complex) :
    realTrace (A - B) = realTrace A - realTrace B := by sorry
