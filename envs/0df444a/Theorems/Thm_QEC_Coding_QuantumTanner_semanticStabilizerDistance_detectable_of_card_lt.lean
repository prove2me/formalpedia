-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_semanticStabilizerDistance_detectable_of_card_lt
-- name    : QEC.Coding.QuantumTanner.semanticStabilizerDistance_detectable_of_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:43:52.538737+00:00
-- url     : https://prove2.me/theorems/6d7d10f0-ec11-4352-9b51-78fcae045512
-- title:
--   Quantum Tanner: semantic Stabilizer Distance detectable of card lt
-- statement:
--   A binary semantic stabilizer distance controls arbitrary operators, not
--   only Pauli errors: every operator supported on fewer than `distance` qubits is
--   detectable on the same source-valid code.  The proof passes through the
--   repository's concrete erasure-recovery theorem and then uses exact erasure
--   recovery to detect every operator on the erased subsystem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8797-L8822
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8797-L8822

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

theorem QEC.Coding.QuantumTanner.semanticStabilizerDistance_detectable_of_card_lt
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (Q : StabilizerCode.SourceValidBinary iota) {distance : Nat}
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q distance)
    (region : Semantics.QuditSubsystem
      (QEC.QLDPC.uniformQuditDimensions (ι := iota) 2))
    (hcard : Fintype.card region.SelectedCoordinates < distance)
    (localOperator : Semantics.Operator region.selectedSystem) :
    Semantics.DetectableOn Q.1.code
      (region.extendLocalToRegister localOperator) := by sorry
