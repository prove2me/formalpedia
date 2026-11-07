-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_localityProfile
-- name    : QEC.Coding.QuantumTanner.Family.ofData_localityProfile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:36:40.325848+00:00
-- url     : https://prove2.me/theorems/3857ea49-be08-486f-b40e-a758434cf4f1
-- title:
--   Family: of Data locality Profile
-- statement:
--   The family observation uses exactly the boundary incidence of the member's
--   Quantum Tanner chain complex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9793-L9799
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9793-L9799

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
open QEC.Coding.QuantumTanner.Family
variable {Index : Type u}
variable {G A B Square XBasis ZBasis : Index → Type v}
variable [∀ i, Group (G i)] [∀ i, Fintype (G i)]
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
variable [∀ i, Fintype (Square i)] [∀ i, DecidableEq (Square i)]
variable [∀ i, Fintype (XBasis i)] [∀ i, Fintype (ZBasis i)]

theorem QEC.Coding.QuantumTanner.Family.ofData_localityProfile
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (hcofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength) (i : Index) :
    (ofData family hcofinal).localityProfile i =
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (family i).chainComplex).localityProfile := by sorry
