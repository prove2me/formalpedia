-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_supported_decomposition_of_cover
-- name    : QEC.Coding.QuantumTanner.exists_supported_decomposition_of_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:41:20.161991+00:00
-- url     : https://prove2.me/theorems/2d07fab5-6b01-46fc-a904-9f15b1553839
-- title:
--   Quantum Tanner: exists supported decomposition of cover
-- statement:
--   An actual small support cover yields row/column-code parts supported on
--   those same sets, as used in [LZ22, Lemma lem:d/2 and proof of thm:main].
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L5145-L5162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L5145-L5162

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

theorem QEC.Coding.QuantumTanner.exists_supported_decomposition_of_cover
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (distanceA distanceB : Nat)
    (hDistanceA : HasMinimumDistanceAtLeast CA distanceA)
    (hDistanceB : HasMinimumDistanceAtLeast CB distanceB)
    (x : Word (ZMod 2) (A × B)) (hx : x ∈ (dualTensorCode CA CB).carrier)
    (rows : Finset A) (columns : Finset B)
    (hRows : rows.card < distanceA) (hColumns : columns.card < distanceB)
    (hCovered : SupportCovered x rows columns) :
    ∃ rowPart columnPart : Word (ZMod 2) (A × B),
      rowPart ∈ (rowCode (A := A) CB).carrier ∧
      columnPart ∈ (columnCode (B := B) CA).carrier ∧
      x = rowPart + columnPart ∧
      (∀ a, a ∉ rows → rowRestriction a rowPart = 0) ∧
      (∀ b, b ∉ columns → columnRestriction b columnPart = 0) := by sorry
