-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_HammingWeight_localExtension_le
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.HammingWeight_localExtension_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:29:56.006538+00:00
-- url     : https://prove2.me/theorems/aee633ce-3f03-4879-8820-d4c8ffdf9abd
-- title:
--   Left Right Cayley Square Complex: Hamming Weight local Extension le
-- statement:
--   Extending a local link word by zero cannot increase its support beyond
--   the `|A| |B|` squares in that link.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9226-L9235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9226-L9235

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
open QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.HammingWeight_localExtension_le
    {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
    [Fintype Square]
    (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) (x : Word (ZMod 2) (A × B)) :
    HammingWeight (X.localExtension vertex x) ≤
      Fintype.card A * Fintype.card B := by sorry
