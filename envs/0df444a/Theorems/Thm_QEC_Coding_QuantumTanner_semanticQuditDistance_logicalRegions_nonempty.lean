-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_semanticQuditDistance_logicalRegions_nonempty
-- name    : QEC.Coding.QuantumTanner.semanticQuditDistance_logicalRegions_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:43:54.121001+00:00
-- url     : https://prove2.me/theorems/2b8915ee-01c7-46af-a5d8-7e8fea25965a
-- title:
--   Quantum Tanner: semantic Qudit Distance logical Regions nonempty
-- statement:
--   An attained binary semantic stabilizer distance supplies a genuine
--   nondetectable finite-region operator for the repository's general qudit
--   distance.  The Pauli witness is pulled back along the full-region local
--   extension, whose surjectivity is proved for positive local dimensions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8866-L8884
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8866-L8884

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

theorem QEC.Coding.QuantumTanner.semanticQuditDistance_logicalRegions_nonempty
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (Q : StabilizerCode.SourceValidBinary iota) {distance : Nat}
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q distance) :
    {weight : Nat |
      ∃ region : Semantics.QuditSubsystem (fun _ : iota => 2),
        Fintype.card region.SelectedCoordinates = weight ∧
          QEC.QLDPC.SupportsNondetectableLocalOperator Q.1.code region}.Nonempty := by sorry
