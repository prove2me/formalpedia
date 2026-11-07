-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_lowWeight_kernel_of_not_codeB_distance
-- name    : QEC.Coding.QuantumTanner.exists_lowWeight_kernel_of_not_codeB_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:24:01.106549+00:00
-- url     : https://prove2.me/theorems/245f98ea-ddd7-48c0-81a0-8738fe3714a5
-- title:
--   Quantum Tanner: exists low Weight kernel of not code B distance
-- statement:
--   Failure of the kernel code's distance bound is witnessed by a nonzero
--   low-weight input annihilated by the second random matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L2143-L2156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L2143-L2156

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

theorem QEC.Coding.QuantumTanner.exists_lowWeight_kernel_of_not_codeB_distance
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (hDistance :
      ¬HasMinimumDistanceAtLeast sample.codeB distance) :
    ∃ target : BinaryLowWeightWords B distance,
      target.1 ≠ 0 ∧ Matrix.mulVec sample.2 target.1 = 0 := by sorry
