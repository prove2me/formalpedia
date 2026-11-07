-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_rankFailureWitness_of_not_fullRowRank
-- name    : QEC.Coding.QuantumTanner.exists_rankFailureWitness_of_not_fullRowRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:22:38.112198+00:00
-- url     : https://prove2.me/theorems/7fe39247-18ab-443f-9e49-2b92f0092fe6
-- title:
--   Quantum Tanner: exists rank Failure Witness of not full Row Rank
-- statement:
--   If either matrix in a random local-code sample loses full row rank, the
--   failure is witnessed by a nonzero vanishing row combination in that matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L1955-L1966
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L1955-L1966

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

theorem QEC.Coding.QuantumTanner.exists_rankFailureWitness_of_not_fullRowRank
    {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    {sample : RandomLocalCodeSample r A B}
    (hFull : ¬sample.HasFullRowRank) :
    (∃ coefficients : ULift.{v} (Fin r) → ZMod 2,
      coefficients ≠ 0 ∧ Matrix.vecMul coefficients sample.1 = 0) ∨
    (∃ coefficients : ULift.{v} (Fin r) → ZMod 2,
      coefficients ≠ 0 ∧ Matrix.vecMul coefficients sample.2 = 0) := by sorry
