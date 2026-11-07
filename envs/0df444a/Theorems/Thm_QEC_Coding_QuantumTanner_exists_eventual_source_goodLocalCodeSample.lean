-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_eventual_source_goodLocalCodeSample
-- name    : QEC.Coding.QuantumTanner.exists_eventual_source_goodLocalCodeSample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:41:45.675604+00:00
-- url     : https://prove2.me/theorems/a27ad659-e106-4e90-b0a8-2ce56a966b56
-- title:
--   Quantum Tanner: exists eventual source good Local Code Sample
-- statement:
--   Choose one joint generator/check sample with the source local conditions.
--   The robustness theorem is applied at epsilon/2 to obtain the larger weight
--   required by LZ22 Theorem thm:123; no square-complex or global-distance conclusion
--   is asserted here.  The distance parameter is in the explicit lower GV branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L7659-L7681
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L7659-L7681

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

theorem QEC.Coding.QuantumTanner.exists_eventual_source_goodLocalCodeSample
    (epsilon gamma delta rho : ℝ) (hEpsilon : 0 < epsilon)
    (hEpsilonUpper : epsilon < 1 / 2)
    (_hGammaLower : 1 / 2 + epsilon < gamma) (hGamma : gamma < 1)
    (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
        Fintype.card A = n → Fintype.card B = n →
          ∃ sample : RandomLocalCodeSample (randomRowCount rho n) A B,
            GoodLocalCodeEvent
              (randomRowCount rho n) (n - randomRowCount rho n)
              (Nat.ceil (delta * n))
              (Nat.floor ((n : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2)))
              (Nat.floor ((n : ℝ) ^ gamma)) sample := by sorry
