-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_kronecker_posDef
-- name    : QEC.Semantics.FiniteMatrixEntropy.logMatrix_kronecker_posDef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:46:36.959892+00:00
-- url     : https://prove2.me/theorems/52de5b97-1057-41b4-b2fa-d655b9c74652
-- title:
--   Finite Matrix Entropy: log Matrix kronecker pos Def
-- statement:
--   The Finite Matrix Entropy construction uses the log Matrix kronecker pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L218-L334
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L218-L334

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
set_option maxHeartbeats 2000000

theorem QEC.Semantics.FiniteMatrixEntropy.logMatrix_kronecker_posDef {m : Type v} {n : Type w}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m Complex) (B : Matrix n n Complex)
    (hA : A.PosDef) (hB : B.PosDef) :
    logMatrix (A ⊗ₖ B) (hA.kronecker hB).isHermitian =
      logMatrix A hA.isHermitian ⊗ₖ 1 + 1 ⊗ₖ logMatrix B hB.isHermitian := by sorry
