-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_dimensions_and_distances_of_ball_bound
-- name    : QEC.Coding.QuantumTanner.hasPositiveUniformProbability_dimensions_and_distances_of_ball_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:04:15.544338+00:00
-- url     : https://prove2.me/theorems/36415dd3-7c05-46d9-bd7f-2dd23deb8a64
-- title:
--   Quantum Tanner: has Positive Uniform Probability dimensions and distances of ball bound
-- statement:
--   The source-facing finite volume criterion selects one pair with the exact
--   local dimensions and the four distance bounds.  Its remaining numerical
--   input is only the binomial Hamming-ball sum, rather than the cardinality of
--   the entire matrix-pair sample space.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L3527-L3548
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L3527-L3548

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

theorem QEC.Coding.QuantumTanner.hasPositiveUniformProbability_dimensions_and_distances_of_ball_bound
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : 0 < r) (hrDelta : r ≤ Delta)
    (hball :
      2 * (2 ^ r - 1) +
          2 * ((2 ^ r - 1) *
            (∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight)) +
          2 * ((∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight) * 2 ^ (Delta - r)) <
        2 ^ Delta) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        Dimension sample.codeA = r ∧
          Dimension sample.codeB = Delta - r ∧
          HasMinimumDistanceAtLeast sample.codeA distance ∧
          HasMinimumDistanceAtLeast sample.codeB distance ∧
          HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
          HasMinimumDistanceAtLeast sample.codeB.dual distance) := by sorry
