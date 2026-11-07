-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_codeA_distance_of_ball_count
-- name    : QEC.Coding.QuantumTanner.hasPositiveUniformProbability_codeA_distance_of_ball_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:40:25.670393+00:00
-- url     : https://prove2.me/theorems/7721f826-4161-4cf0-9550-82c4a8f499b8
-- title:
--   Quantum Tanner: has Positive Uniform Probability code A distance of ball count
-- statement:
--   With a nonempty row set, the generator-code distance event's exact
--   matrix-fiber count reduces to its finite Hamming-ball numerator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L2026-L2062
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L2026-L2062

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

theorem QEC.Coding.QuantumTanner.hasPositiveUniformProbability_codeA_distance_of_ball_count
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hRows : 0 < r)
    (hball :
      (2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance, Nat.choose Delta weight) <
          2 ^ Delta) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        HasMinimumDistanceAtLeast sample.codeA distance) := by sorry
