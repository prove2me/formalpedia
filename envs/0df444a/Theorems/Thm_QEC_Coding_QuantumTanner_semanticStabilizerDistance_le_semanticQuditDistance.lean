-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_semanticStabilizerDistance_le_semanticQuditDistance
-- name    : QEC.Coding.QuantumTanner.semanticStabilizerDistance_le_semanticQuditDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:45:35.613296+00:00
-- url     : https://prove2.me/theorems/8fa0a849-9f14-4a52-b57e-8ec2687e0c30
-- title:
--   Quantum Tanner: semantic Stabilizer Distance le semantic Qudit Distance
-- statement:
--   The binary semantic stabilizer distance lower-bounds the repository's
--   general local-operator semantic distance on the same qubit code.  Unlike the
--   attained-infimum helper above, this bridge needs no separate nonemptiness
--   hypothesis: the attained Pauli witness supplies it on the full region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8890-L8897
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8890-L8897

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

theorem QEC.Coding.QuantumTanner.semanticStabilizerDistance_le_semanticQuditDistance
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (Q : StabilizerCode.SourceValidBinary iota) {distance : Nat}
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q distance) :
    distance ≤ QEC.QLDPC.semanticQuditDistance
      (fun _ : iota => 2) Q.1.code := by sorry
