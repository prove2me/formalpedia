-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_dimension_codeA_of_goodLocalCodeEvent
-- name    : QEC.Coding.QuantumTanner.dimension_codeA_of_goodLocalCodeEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:42:32.196158+00:00
-- url     : https://prove2.me/theorems/5f14c4fe-b39d-4f5c-b2f7-0d0bea63f183
-- title:
--   Quantum Tanner: dimension code A of good Local Code Event
-- statement:
--   The successful event records the exact dimension of the generator-code
--   half of the local pair.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8666-L8673
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8666-L8673

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

theorem QEC.Coding.QuantumTanner.dimension_codeA_of_goodLocalCodeEvent
    {r dimensionA dimensionB distanceThreshold robustness punctures : Nat}
    {A B : Type v} [Fintype A] [Fintype B]
    {sample : RandomLocalCodeSample r A B}
    (hgood : GoodLocalCodeEvent
      dimensionA dimensionB distanceThreshold robustness punctures sample) :
    Dimension sample.codeA = dimensionA := by sorry
