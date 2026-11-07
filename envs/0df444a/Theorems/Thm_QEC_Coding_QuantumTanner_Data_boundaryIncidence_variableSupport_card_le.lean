-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_boundaryIncidence_variableSupport_card_le
-- name    : QEC.Coding.QuantumTanner.Data.boundaryIncidence_variableSupport_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:29:32.644037+00:00
-- url     : https://prove2.me/theorems/f34fb55f-f3af-4043-8879-1e3fd14618d9
-- title:
--   Data: boundary Incidence variable Support card le
-- statement:
--   The actual Quantum Tanner boundary incidence has the source-local variable
--   degree bound obtained by counting the two incident vertices on each side.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9430-L9438
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9430-L9438

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

theorem QEC.Coding.QuantumTanner.Data.boundaryIncidence_variableSupport_card_le
    (D : Data G A B Square XBasis ZBasis) (square : Square) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).variableSupport
      square).card ≤
        2 * Fintype.card XBasis + 2 * Fintype.card ZBasis := by sorry
