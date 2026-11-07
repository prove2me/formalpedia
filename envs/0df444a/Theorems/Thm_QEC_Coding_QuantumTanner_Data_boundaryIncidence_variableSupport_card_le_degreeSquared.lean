-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_boundaryIncidence_variableSupport_card_le_degreeSquared
-- name    : QEC.Coding.QuantumTanner.Data.boundaryIncidence_variableSupport_card_le_degreeSquared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:46:56.187117+00:00
-- url     : https://prove2.me/theorems/3083cd6f-f6e9-4764-a5f4-3c29b46e7389
-- title:
--   Data: boundary Incidence variable Support card le degree Squared
-- statement:
--   The arithmetic core of the LZ22 variable-incidence estimate.  When the
--   two local codes have complementary dimensions `r` and `Delta - r`, both
--   selected tensor-code bases have size `r * (Delta - r)`, so the two incident
--   vertices on each side contribute at most `4 * r * (Delta - r) ≤ Delta²`.
--
--   The tensor-code dimension equalities are discharged here from the source
--   dimensions of the two local codes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9458-L9494
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9458-L9494

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

theorem QEC.Coding.QuantumTanner.Data.boundaryIncidence_variableSupport_card_le_degreeSquared
    (D : Data G A B Square XBasis ZBasis) (Delta r : Nat)
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : r ≤ Delta)
    (hCodeA : Dimension D.codeA = r)
    (hCodeB : Dimension D.codeB = Delta - r)
    (square : Square) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).variableSupport
      square).card ≤ Delta * Delta := by sorry
