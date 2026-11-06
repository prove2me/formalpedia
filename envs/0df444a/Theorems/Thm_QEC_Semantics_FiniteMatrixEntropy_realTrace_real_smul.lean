-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_real_smul
-- name    : QEC.Semantics.FiniteMatrixEntropy.realTrace_real_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:18:47.874206+00:00
-- url     : https://prove2.me/theorems/5558848d-2013-4aee-81e7-0ca0357a4361
-- title:
--   Finite Matrix Entropy: real Trace real smul
-- statement:
--   Real scalar multiplication commutes with the real trace pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L490-L497
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L490-L497

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

theorem QEC.Semantics.FiniteMatrixEntropy.realTrace_real_smul {n : Type v} [Fintype n]
    (s : Real) (A : Matrix n n Complex) :
    realTrace (s • A) = s * realTrace A := by sorry
