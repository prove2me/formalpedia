-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_boundaryStabilizerFamily_isLDPC_degreeSquared
-- name    : QEC.Coding.QuantumTanner.Data.boundaryStabilizerFamily_isLDPC_degreeSquared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:48:04.559487+00:00
-- url     : https://prove2.me/theorems/717d7600-ffb0-49c2-b983-16d80d1cb753
-- title:
--   Data: boundary Stabilizer Family is LDPC degree Squared
-- statement:
--   A family of Quantum Tanner data at one fixed degree, with the source's
--   complementary local-code dimensions, is an LDPC family of source-valid
--   stabilizer codes with the uniform bound `Delta²`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9602-L9639
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9602-L9639

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

theorem QEC.Coding.QuantumTanner.Data.boundaryStabilizerFamily_isLDPC_degreeSquared
    {Index : Type u}
    {Gf Af Bf Squaref XBasisf ZBasisf : Index → Type v}
    [∀ i, Group (Gf i)] [∀ i, Fintype (Gf i)]
    [∀ i, Fintype (Af i)] [∀ i, Fintype (Bf i)]
    [∀ i, Fintype (Squaref i)]
    [∀ i, Fintype (XBasisf i)] [∀ i, Fintype (ZBasisf i)]
    (family : ∀ i, Data (Gf i) (Af i) (Bf i) (Squaref i)
      (XBasisf i) (ZBasisf i))
    (Delta r : Nat)
    (hA : ∀ i, Fintype.card (Af i) = Delta)
    (hB : ∀ i, Fintype.card (Bf i) = Delta)
    (hr : r ≤ Delta)
    (hCodeA : ∀ i, Dimension (family i).codeA = r)
    (hCodeB : ∀ i, Dimension (family i).codeB = Delta - r) :
    QEC.QLDPC.IsLDPCStabilizerFamily
      (fun i => (family i).chainComplex.binaryCSSSourceValidStabilizer) := by sorry
