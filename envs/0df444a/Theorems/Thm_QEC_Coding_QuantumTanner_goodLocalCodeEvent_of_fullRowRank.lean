-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_goodLocalCodeEvent_of_fullRowRank
-- name    : QEC.Coding.QuantumTanner.goodLocalCodeEvent_of_fullRowRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:41:38.5202+00:00
-- url     : https://prove2.me/theorems/4fe1f290-d298-4ab2-9713-7d26e057a7f4
-- title:
--   Quantum Tanner: good Local Code Event of full Row Rank
-- statement:
--   Full row rank discharges both dimension clauses of the successful event;
--   the remaining hypotheses are precisely the primal/dual GV-distance and
--   puncture-resistant robustness estimates proved by the source's probabilistic
--   argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L7123-L7144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L7123-L7144

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

theorem QEC.Coding.QuantumTanner.goodLocalCodeEvent_of_fullRowRank
    {r Delta distanceThreshold robustness punctures : Nat}
    {A B : Type v} [Fintype A] [Fintype B]
    {sample : RandomLocalCodeSample r A B}
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hFull : sample.HasFullRowRank)
    (hDistanceA : HasMinimumDistanceAtLeast sample.codeA distanceThreshold)
    (hDistanceB : HasMinimumDistanceAtLeast sample.codeB distanceThreshold)
    (hDistanceADual :
      HasMinimumDistanceAtLeast sample.codeA.dual distanceThreshold)
    (hDistanceBDual :
      HasMinimumDistanceAtLeast sample.codeB.dual distanceThreshold)
    (hRobust : IsRobustWithPunctureResistance
      sample.codeA sample.codeB robustness punctures)
    (hRobustDual : IsRobustWithPunctureResistance
      sample.codeA.dual sample.codeB.dual robustness punctures) :
    GoodLocalCodeEvent
      r (Delta - r) distanceThreshold robustness punctures sample := by sorry
