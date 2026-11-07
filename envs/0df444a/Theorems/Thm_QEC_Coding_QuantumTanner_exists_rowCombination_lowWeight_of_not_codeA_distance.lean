-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_rowCombination_lowWeight_of_not_codeA_distance
-- name    : QEC.Coding.QuantumTanner.exists_rowCombination_lowWeight_of_not_codeA_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:23:47.295521+00:00
-- url     : https://prove2.me/theorems/0c5099d8-9548-4744-af3b-22137559ffb3
-- title:
--   Quantum Tanner: exists row Combination low Weight of not code A distance
-- statement:
--   Failure of the generator-row code's distance bound is witnessed by a
--   nonzero row combination attaining a nonzero low-weight binary word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L1392-L1419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L1392-L1419

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

theorem QEC.Coding.QuantumTanner.exists_rowCombination_lowWeight_of_not_codeA_distance
    {r distance : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B)
    (hDistance :
      ¬HasMinimumDistanceAtLeast sample.codeA distance) :
    ∃ coefficients : ULift.{v} (Fin r) → ZMod 2,
      coefficients ≠ 0 ∧
      ∃ target : BinaryLowWeightWords A distance,
        target.1 ≠ 0 ∧
        Matrix.vecMul coefficients sample.1 = target.1 := by sorry
