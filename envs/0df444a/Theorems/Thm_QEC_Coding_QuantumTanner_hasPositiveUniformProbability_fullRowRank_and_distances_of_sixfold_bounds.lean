-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_fullRowRank_and_distances_of_sixfold_bounds
-- name    : QEC.Coding.QuantumTanner.hasPositiveUniformProbability_fullRowRank_and_distances_of_sixfold_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:40:48.339099+00:00
-- url     : https://prove2.me/theorems/05684621-9c5d-4e79-b172-e704acec8b03
-- title:
--   Quantum Tanner: has Positive Uniform Probability full Row Rank and distances of sixfold bounds
-- statement:
--   Sixfold bounds on the rank, generator-distance, and kernel-distance
--   numerators give one positive-probability local-code draw satisfying all
--   five finite rank/distance requirements simultaneously.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L3249-L3272
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L3249-L3272

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

theorem QEC.Coding.QuantumTanner.hasPositiveUniformProbability_fullRowRank_and_distances_of_sixfold_bounds
    {r Delta distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : 0 < r) (hrDelta : r ≤ Delta)
    (hRank : 6 * (2 ^ r - 1) < 2 ^ Delta)
    (hGenerator :
      6 * ((2 ^ r - 1) *
        (∑ weight ∈ Finset.range distance,
          Nat.choose Delta weight)) < 2 ^ Delta)
    (hKernel :
      6 * ((∑ weight ∈ Finset.range distance,
        Nat.choose Delta weight) * 2 ^ (Delta - r)) < 2 ^ Delta) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample r A B =>
        sample.HasFullRowRank ∧
          HasMinimumDistanceAtLeast sample.codeA distance ∧
          HasMinimumDistanceAtLeast sample.codeB distance ∧
          HasMinimumDistanceAtLeast sample.codeA.dual distance ∧
          HasMinimumDistanceAtLeast sample.codeB.dual distance) := by sorry
