-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_boundaryIncidence_boundedLocality_degreeSquared_of_goodLocalCodeEvent
-- name    : QEC.Coding.QuantumTanner.Data.boundaryIncidence_boundedLocality_degreeSquared_of_goodLocalCodeEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:48:05.25098+00:00
-- url     : https://prove2.me/theorems/3192d045-e5f2-4174-8f71-156c9fc518a1
-- title:
--   Data: boundary Incidence bounded Locality degree Squared of good Local Code Event
-- statement:
--   A successful LZ22 local-code draw supplies the dimension hypotheses needed
--   for the construction's exact `Delta²` locality bound.  The equalities below
--   identify the fixed draw with the two local codes stored by the concrete
--   Quantum Tanner data; no conclusion about an unselected complex is used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9580-L9597
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9580-L9597

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
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]

theorem QEC.Coding.QuantumTanner.Data.boundaryIncidence_boundedLocality_degreeSquared_of_goodLocalCodeEvent
    (D : Data G A B Square XBasis ZBasis)
    {Delta r distanceThreshold robustness punctures : Nat}
    (sample : RandomLocalCodeSample r A B)
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : r ≤ Delta)
    (hCodeA : D.codeA = sample.codeA)
    (hCodeB : D.codeB = sample.codeB)
    (hgood : GoodLocalCodeEvent
      r (Delta - r) distanceThreshold robustness punctures sample) :
    QEC.Coding.BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile
      (Delta * Delta) := by sorry
