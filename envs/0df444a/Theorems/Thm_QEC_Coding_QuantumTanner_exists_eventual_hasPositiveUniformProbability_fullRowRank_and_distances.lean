-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_eventual_hasPositiveUniformProbability_fullRowRank_and_distances
-- name    : QEC.Coding.QuantumTanner.exists_eventual_hasPositiveUniformProbability_fullRowRank_and_distances
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T02:03:08.871206+00:00
-- url     : https://prove2.me/theorems/d31bd8b3-9a86-45ad-acff-5f747883d7c8
-- title:
--   Quantum Tanner: exists eventual has Positive Uniform Probability full Row Rank and distances
-- statement:
--   At every sufficiently large fixed degree, the corrected local entropy
--   hypothesis yields one positive-probability draw satisfying the two full-rank
--   and four distance conditions simultaneously.  The degree remains a local
--   parameter here; selecting the source's square-complex family is separate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L3320-L3349
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L3320-L3349

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

theorem QEC.Coding.QuantumTanner.exists_eventual_hasPositiveUniformProbability_fullRowRank_and_distances
    (rho delta : ℝ) (hRhoPositive : 0 < rho)
    (hRhoHalf : rho < 1 / 2) (hdeltaPositive : 0 < delta)
    (hdeltaHalf : delta < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ (Delta : Nat), threshold ≤ Delta →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
        Fintype.card A = Delta → Fintype.card B = Delta →
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
