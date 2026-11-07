-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_semanticStabilizerDistance_le_card_of_nondetectable
-- name    : QEC.Coding.QuantumTanner.semanticStabilizerDistance_le_card_of_nondetectable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:44:21.900639+00:00
-- url     : https://prove2.me/theorems/e61b79c4-5bf2-41d4-91f2-9e8185a5cde4
-- title:
--   Quantum Tanner: semantic Stabilizer Distance le card of nondetectable
-- statement:
--   Every concrete region supporting a nondetectable local operator has at
--   least the binary semantic stabilizer distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8826-L8839
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8826-L8839

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

theorem QEC.Coding.QuantumTanner.semanticStabilizerDistance_le_card_of_nondetectable
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (Q : StabilizerCode.SourceValidBinary iota) {distance : Nat}
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q distance)
    (region : Semantics.QuditSubsystem
      (QEC.QLDPC.uniformQuditDimensions (ι := iota) 2))
    (hregion : QEC.QLDPC.SupportsNondetectableLocalOperator Q.1.code region) :
    distance ≤ Fintype.card region.SelectedCoordinates := by sorry
