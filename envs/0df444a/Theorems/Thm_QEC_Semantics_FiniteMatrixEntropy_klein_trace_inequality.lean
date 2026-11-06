-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_klein_trace_inequality
-- name    : QEC.Semantics.FiniteMatrixEntropy.klein_trace_inequality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:39:04.459436+00:00
-- url     : https://prove2.me/theorems/1ee50419-56fd-4eac-8f64-bdd5ea101ec1
-- title:
--   Finite Matrix Entropy: klein trace inequality
-- statement:
--   Finite noncommutative Klein trace inequality.  `A` and `B` are diagonalized
--   independently; their interaction is represented by the doubly stochastic
--   overlap weights between the two eigenbases.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L351-L403
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L351-L403

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

theorem QEC.Semantics.FiniteMatrixEntropy.klein_trace_inequality {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n Complex) (hA : A.PosSemidef) (hB : B.PosDef) :
    realTrace (A - B) <= relativeEntropy A B hA.isHermitian hB.isHermitian := by sorry
