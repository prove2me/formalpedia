-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_codeB_distance_of_entropy_margin
-- name    : QEC.Coding.QuantumTanner.hasPositiveUniformProbability_codeB_distance_of_entropy_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:02:16.971986+00:00
-- url     : https://prove2.me/theorems/ff43a6a3-a032-4965-ba10-48be34aa19e9
-- title:
--   Quantum Tanner: has Positive Uniform Probability code B distance of entropy margin
-- statement:
--   The exact Hamming-ball count, the entropy estimate, and the one-row
--   flooring margin together yield positive probability of the kernel local
--   code's prescribed relative distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L2360-L2382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L2360-L2382

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

theorem QEC.Coding.QuantumTanner.hasPositiveUniformProbability_codeB_distance_of_entropy_margin
    {Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (rho delta : ℝ) (hA : Fintype.card A = Delta)
    (hB : Fintype.card B = Delta) (hDelta : 0 < Delta)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hceil : 2 ≤ Nat.ceil (delta * Delta))
    (hmargin : Real.log 2 <
      (rho * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ)) :
    HasPositiveUniformProbability
      (fun sample : RandomLocalCodeSample (randomRowCount rho Delta) A B =>
        HasMinimumDistanceAtLeast sample.codeB
          (Nat.ceil (delta * Delta))) := by sorry
