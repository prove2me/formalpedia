-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_RawData_boundary1_basis_support_subset
-- name    : QEC.Coding.QuantumTanner.RawData.boundary1_basis_support_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:46:35.319868+00:00
-- url     : https://prove2.me/theorems/86643836-2853-42de-9e81-74dc36d08336
-- title:
--   Raw Data: boundary1 basis support subset
-- statement:
--   A boundary-one column can meet only X checks based at the two side-one
--   vertices incident to the square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9308-L9340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9308-L9340

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

theorem QEC.Coding.QuantumTanner.RawData.boundary1_basis_support_subset
    (D : RawData G A B Square XBasis ZBasis) (square : Square) :
    hammingSupport
        (D.boundary1 (canonicalBasisWord (F := ZMod 2) square)) ⊆
      ((Finset.univ.filter fun g => D.complex.Incident (g, true) square).product
        (Finset.univ : Finset XBasis)) := by sorry
