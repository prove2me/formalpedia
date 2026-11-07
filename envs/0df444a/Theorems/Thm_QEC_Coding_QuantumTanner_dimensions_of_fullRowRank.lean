-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_dimensions_of_fullRowRank
-- name    : QEC.Coding.QuantumTanner.dimensions_of_fullRowRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:28:07.664357+00:00
-- url     : https://prove2.me/theorems/6cbe3a2d-6be9-47ad-9936-5b371c332866
-- title:
--   Quantum Tanner: dimensions of full Row Rank
-- statement:
--   Full row rank supplies the exact complementary local dimensions in the
--   successful random event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L3475-L3485
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L3475-L3485

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

theorem QEC.Coding.QuantumTanner.dimensions_of_fullRowRank
    {r Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (_hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hFull : sample.HasFullRowRank) :
    Dimension sample.codeA = r ∧ Dimension sample.codeB = Delta - r := by sorry
