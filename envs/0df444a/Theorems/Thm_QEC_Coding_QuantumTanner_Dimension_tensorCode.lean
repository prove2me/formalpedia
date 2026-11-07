-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Dimension_tensorCode
-- name    : QEC.Coding.QuantumTanner.Dimension_tensorCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:26:21.888021+00:00
-- url     : https://prove2.me/theorems/eb26b961-7dce-49cb-bbc2-d66aa5ce9dea
-- title:
--   Quantum Tanner: Dimension tensor Code
-- statement:
--   The concrete row-and-column tensor code has the expected product
--   dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L1043-L1051
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L1043-L1051

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

theorem QEC.Coding.QuantumTanner.Dimension_tensorCode
    {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) :
    Dimension (tensorCode CA CB) = Dimension CA * Dimension CB := by sorry
