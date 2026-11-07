-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_RawData_HammingWeight_transpose_boundary2_basis_le
-- name    : QEC.Coding.QuantumTanner.RawData.HammingWeight_transpose_boundary2_basis_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:46:07.265145+00:00
-- url     : https://prove2.me/theorems/d7464257-5adc-4b4c-88cd-726526e55f84
-- title:
--   Raw Data: Hamming Weight transpose boundary2 basis le
-- statement:
--   Each square is incident to at most two copies of every selected Z-basis
--   check.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9401-L9418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9401-L9418

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
open QEC.Coding.QuantumTanner.RawData
variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]

theorem QEC.Coding.QuantumTanner.RawData.HammingWeight_transpose_boundary2_basis_le
    (D : RawData G A B Square XBasis ZBasis) (square : Square) :
    HammingWeight
        (wordLinearMapTranspose D.boundary2
          (canonicalBasisWord (F := ZMod 2) square)) ≤
      2 * Fintype.card ZBasis := by sorry
