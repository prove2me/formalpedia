-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_semanticQuditDistance_ge_of_hasParameters
-- name    : QEC.Coding.QuantumTanner.Data.semanticQuditDistance_ge_of_hasParameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:47:16.822828+00:00
-- url     : https://prove2.me/theorems/e6c3a333-06e5-4de8-9834-0f95fc2a6172
-- title:
--   Data: semantic Qudit Distance ge of has Parameters
-- statement:
--   The distance component of `Data.HasParameters` is also a lower bound for
--   the repository's general local-operator semantic distance.  This is the
--   finite-code distance bridge needed by the eventual Quantum Tanner family:
--   the algebraic CSS minimum first gives the attained Pauli distance, and the
--   full-region argument above supplies attainment for arbitrary local
--   operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9662-L9670
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9662-L9670

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]
variable [DecidableEq Square]

theorem QEC.Coding.QuantumTanner.Data.semanticQuditDistance_ge_of_hasParameters
    (D : Data G A B Square XBasis ZBasis) {n k distance : Nat}
    (hParameters : D.HasParameters n k distance) :
    distance ≤ QEC.QLDPC.semanticQuditDistance
      (fun _ : Square => 2)
      D.chainComplex.binaryCSSSourceValidStabilizer.1.code := by sorry
