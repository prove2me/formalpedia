-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_codeA_dual_distance_of_count_bound
-- name    : QEC.Coding.QuantumTanner.hasPositiveUniformProbability_codeA_dual_distance_of_count_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T02:03:28.968189+00:00
-- url     : https://prove2.me/theorems/09bbb820-8f1c-46f3-a6f5-1121b3ed051d
-- title:
--   Quantum Tanner: has Positive Uniform Probability code A dual distance of count bound
-- statement:
--   The first random row code's dual is the first-matrix kernel.  Swapping
--   the matrices therefore transfers the proved kernel-distance probability to
--   `codeA.dual`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L2481-L2508
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L2481-L2508

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

theorem QEC.Coding.QuantumTanner.hasPositiveUniformProbability_codeA_dual_distance_of_count_bound
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hcount :
      (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) *
          (2 ^ (r * Delta) * 2 ^ (r * Delta - r)) <
        2 ^ (r * Delta) * 2 ^ (r * Delta)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        HasMinimumDistanceAtLeast sample.codeA.dual distance) := by sorry
