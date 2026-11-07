-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_fullRowRank_and_distances_of_entropy_margins
-- name    : QEC.Coding.QuantumTanner.hasPositiveUniformProbability_fullRowRank_and_distances_of_entropy_margins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:40:38.632787+00:00
-- url     : https://prove2.me/theorems/0314e24a-369b-47e9-90d4-9b42064f74c4
-- title:
--   Quantum Tanner: has Positive Uniform Probability full Row Rank and distances of entropy margins
-- statement:
--   Strict finite-degree entropy margins give one random local-code sample
--   with both full-rank matrices and all four primal/dual distance bounds.  In
--   contrast to separate positive-probability statements, this conclusion is
--   about a single simultaneous draw.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L3278-L3314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L3278-L3314

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

theorem QEC.Coding.QuantumTanner.hasPositiveUniformProbability_fullRowRank_and_distances_of_entropy_margins
    {Delta : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (rho delta : ℝ) (hA : Fintype.card A = Delta)
    (hB : Fintype.card B = Delta)
    (hRhoNonnegative : 0 ≤ rho) (hDelta : 0 < Delta)
    (hRows : 0 < randomRowCount rho Delta)
    (hRowsDelta : randomRowCount rho Delta ≤ Delta)
    (hdeltaPositive : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hceil : 2 ≤ Nat.ceil (delta * Delta))
    (hGeneratorGap :
      Real.log 6 <
        ((1 - rho) * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ))
    (hKernelGap :
      Real.log 6 + Real.log 2 <
        (rho * Real.log 2 - Real.binEntropy delta) * (Delta : ℝ)) :
    HasPositiveUniformProbability
      (fun sample :
          RandomLocalCodeSample (randomRowCount rho Delta) A B =>
        sample.HasFullRowRank ∧
          HasMinimumDistanceAtLeast sample.codeA
            (Nat.ceil (delta * Delta)) ∧
          HasMinimumDistanceAtLeast sample.codeB
            (Nat.ceil (delta * Delta)) ∧
          HasMinimumDistanceAtLeast sample.codeA.dual
            (Nat.ceil (delta * Delta)) ∧
          HasMinimumDistanceAtLeast sample.codeB.dual
            (Nat.ceil (delta * Delta))) := by sorry
