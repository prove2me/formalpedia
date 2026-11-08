-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_codeA_distance_of_entropy_gap
-- name    : QEC.Coding.QuantumTanner.hasPositiveUniformProbability_codeA_distance_of_entropy_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:03:24.736556+00:00
-- url     : https://prove2.me/theorems/75d30078-bafc-4be1-b152-6e5d6a54ff01
-- title:
--   Quantum Tanner: has Positive Uniform Probability code A distance of entropy gap
-- statement:
--   The entropy gap below the local generator rate, together with
--   `rho < 1/2`, bounds the generator-code Hamming-ball numerator strictly
--   below the number of binary words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L2067-L2139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L2067-L2139

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

theorem QEC.Coding.QuantumTanner.hasPositiveUniformProbability_codeA_distance_of_entropy_gap
    {Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (rho delta : ℝ) (hA : Fintype.card A = Delta)
    (hB : Fintype.card B = Delta)
    (hRhoNonnegative : 0 ≤ rho) (hRhoHalf : rho < 1 / 2)
    (hDelta : 0 < Delta) (hRows : 0 < randomRowCount rho Delta)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hceil : 2 ≤ Nat.ceil (delta * Delta))
    (hentropy : Real.binEntropy delta < rho * Real.log 2) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample (randomRowCount rho Delta) A B =>
        HasMinimumDistanceAtLeast sample.codeA
          (Nat.ceil (delta * Delta))) := by sorry
