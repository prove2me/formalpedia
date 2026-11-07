-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_tensorCode_induction
-- name    : QEC.Coding.QuantumTanner.tensorCode_induction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:24:37.165996+00:00
-- url     : https://prove2.me/theorems/bb566ee3-8888-4355-a949-3e970155fb4b
-- title:
--   Quantum Tanner: tensor Code induction
-- statement:
--   Induction on actual tensor-code words through pure local-code products.
--   This bridges the row-and-column definition to its tensor-product realization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L1002-L1029
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L1002-L1029

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

theorem QEC.Coding.QuantumTanner.tensorCode_induction
    {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B)
    {P : Word F (A × B) → Prop}
    (hZero : P 0)
    (hAdd : ∀ x y, P x → P y → P (x + y))
    (hPure : ∀ a, a ∈ CA.carrier → ∀ b, b ∈ CB.carrier →
      P (fun ab => a ab.1 * b ab.2))
    (x : Word F (A × B)) (hx : x ∈ (tensorCode CA CB).carrier) : P x := by sorry
