-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_finiteQuditCheckPresentation_distance_ge_of_hasParameters
-- name    : QEC.Coding.QuantumTanner.Data.finiteQuditCheckPresentation_distance_ge_of_hasParameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:47:44.695097+00:00
-- url     : https://prove2.me/theorems/94ea48fc-22b1-4d2f-9c11-b2d5e02420c1
-- title:
--   Data: finite Qudit Check Presentation distance ge of has Parameters
-- statement:
--   Exact Tanner parameters give the same semantic distance lower bound on the
--   concrete finite-qudit presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9730-L9737
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9730-L9737

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

theorem QEC.Coding.QuantumTanner.Data.finiteQuditCheckPresentation_distance_ge_of_hasParameters
    (D : Data G A B Square XBasis ZBasis) {n k distance : Nat}
    (hParameters : D.HasParameters n k distance) :
    distance ≤ D.finiteQuditCheckPresentation.distance := by sorry
