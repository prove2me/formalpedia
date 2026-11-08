-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_goodLocalCodeSample_of_positive
-- name    : QEC.Coding.QuantumTanner.exists_goodLocalCodeSample_of_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:06:19.884351+00:00
-- url     : https://prove2.me/theorems/7168df06-7b2a-45f4-9d8c-820e07fdf928
-- title:
--   Quantum Tanner: exists good Local Code Sample of positive
-- statement:
--   Positive probability of the simultaneous LZ22 local-code event fixes one
--   actual generator/check-matrix sample satisfying every clause of the event.
--   The witness is selected once, before any square-complex family is introduced.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8649-L8662
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8649-L8662

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

theorem QEC.Coding.QuantumTanner.exists_goodLocalCodeSample_of_positive
    {r dimensionA dimensionB distanceThreshold robustness punctures : Nat}
    {A B : Type v} [Fintype A] [Fintype B]
    [DecidablePred (GoodLocalCodeEvent
      (r := r) (A := A) (B := B)
      dimensionA dimensionB distanceThreshold robustness punctures)]
    (hpositive : HasPositiveUniformProbability
      (GoodLocalCodeEvent
        (r := r) (A := A) (B := B)
        dimensionA dimensionB distanceThreshold robustness punctures)) :
    ∃ sample : RandomLocalCodeSample r A B,
      GoodLocalCodeEvent
        dimensionA dimensionB distanceThreshold robustness punctures sample := by sorry
