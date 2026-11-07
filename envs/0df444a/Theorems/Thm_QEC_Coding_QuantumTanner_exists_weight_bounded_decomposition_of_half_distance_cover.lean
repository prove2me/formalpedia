-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_weight_bounded_decomposition_of_half_distance_cover
-- name    : QEC.Coding.QuantumTanner.exists_weight_bounded_decomposition_of_half_distance_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:42:17.233081+00:00
-- url     : https://prove2.me/theorems/ae91be93-8f0f-4e0a-8144-872fd70161f9
-- title:
--   Quantum Tanner: exists weight bounded decomposition of half distance cover
-- statement:
--   A half-distance support cover gives an actual row/column decomposition,
--   with neither part heavier than the original word. This exposes the attained
--   decomposition used in [LZ22, Proposition prop:tensor], not an assumed decoder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L5167-L5193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L5167-L5193

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

theorem QEC.Coding.QuantumTanner.exists_weight_bounded_decomposition_of_half_distance_cover
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (hPositiveA : 0 < distanceA) (hPositiveB : 0 < distanceB)
    (x : Word (ZMod 2) (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier)
    (rows : Finset A) (columns : Finset B)
    (hRows : 2 * rows.card ≤ distanceA)
    (hColumns : 2 * columns.card ≤ distanceB)
    (hCovered : SupportCovered x rows columns) :
    ∃ rowPart columnPart : Word (ZMod 2) (A × B),
      rowPart ∈ (rowCode (A := A) CB).carrier ∧
      columnPart ∈ (columnCode (B := B) CA).carrier ∧
      x = rowPart + columnPart ∧
      HammingWeight rowPart ≤ HammingWeight x ∧
      HammingWeight columnPart ≤ HammingWeight x := by sorry
