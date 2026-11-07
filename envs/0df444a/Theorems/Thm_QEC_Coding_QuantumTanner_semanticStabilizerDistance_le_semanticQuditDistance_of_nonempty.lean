-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_semanticStabilizerDistance_le_semanticQuditDistance_of_nonempty
-- name    : QEC.Coding.QuantumTanner.semanticStabilizerDistance_le_semanticQuditDistance_of_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:44:24.488758+00:00
-- url     : https://prove2.me/theorems/b73b6aca-1e29-4736-9ac2-5479a9a6035f
-- title:
--   Quantum Tanner: semantic Stabilizer Distance le semantic Qudit Distance of nonempty
-- statement:
--   When the repository's finite-region semantic distance is attained, the
--   binary semantic stabilizer distance lower-bounds it on the same code.  The
--   explicit nonemptiness premise is necessary because `semanticQuditDistance`
--   is defined to be zero when no nondetectable region exists.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8845-L8860
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8845-L8860

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

theorem QEC.Coding.QuantumTanner.semanticStabilizerDistance_le_semanticQuditDistance_of_nonempty
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (Q : StabilizerCode.SourceValidBinary iota) {distance : Nat}
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q distance)
    (hnonempty : {weight : Nat |
      ∃ region : Semantics.QuditSubsystem
          (fun _ : iota => 2),
        Fintype.card region.SelectedCoordinates = weight ∧
          QEC.QLDPC.SupportsNondetectableLocalOperator Q.1.code region}.Nonempty) :
    distance ≤ QEC.QLDPC.semanticQuditDistance
      (fun _ : iota => 2) Q.1.code := by sorry
