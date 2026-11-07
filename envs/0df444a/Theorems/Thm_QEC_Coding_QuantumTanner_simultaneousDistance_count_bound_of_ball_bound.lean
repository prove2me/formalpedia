-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_simultaneousDistance_count_bound_of_ball_bound
-- name    : QEC.Coding.QuantumTanner.simultaneousDistance_count_bound_of_ball_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:27:30.945199+00:00
-- url     : https://prove2.me/theorems/005ef102-d13c-4ba8-a28b-4e79bb6dd479
-- title:
--   Quantum Tanner: simultaneous Distance count bound of ball bound
-- statement:
--   Cancel the common power of two from the five-event union bound.  The
--   resulting inequality isolates the Hamming-ball volume, which is the quantity
--   controlled by the source's binary-entropy hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L2809-L2868
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L2809-L2868

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

theorem QEC.Coding.QuantumTanner.simultaneousDistance_count_bound_of_ball_bound
    {r Delta distance : Nat} (hr : 0 < r) (hrDelta : r ≤ Delta)
    (hball :
      2 * (2 ^ r - 1) +
          2 * ((2 ^ r - 1) *
            (∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight)) +
          2 * ((∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight) * 2 ^ (Delta - r)) <
        2 ^ Delta) :
    2 * (2 ^ r - 1) *
          (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta)) +
        2 * (((2 ^ r - 1) *
            (∑ weight ∈ Finset.range distance,
              Nat.choose Delta weight)) *
          (2 ^ (r * Delta - Delta) * 2 ^ (r * Delta))) +
        2 * ((∑ weight ∈ Finset.range distance,
            Nat.choose Delta weight) *
          (2 ^ (r * Delta) * 2 ^ (r * Delta - r))) <
      2 ^ (r * Delta) * 2 ^ (r * Delta) := by sorry
