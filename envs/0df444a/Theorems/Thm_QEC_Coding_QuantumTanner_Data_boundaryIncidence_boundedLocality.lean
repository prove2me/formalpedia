-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_boundaryIncidence_boundedLocality
-- name    : QEC.Coding.QuantumTanner.Data.boundaryIncidence_boundedLocality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:46:20.935203+00:00
-- url     : https://prove2.me/theorems/d969553d-dd92-499f-b5c4-660eb9fdaef6
-- title:
--   Data: boundary Incidence bounded Locality
-- statement:
--   The finite Quantum Tanner presentation has locality controlled by the
--   link size and by the exact number of selected local-basis checks meeting a
--   square.  This is the construction-level input to the uniform family bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9499-L9521
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9499-L9521

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

theorem QEC.Coding.QuantumTanner.Data.boundaryIncidence_boundedLocality
    (D : Data G A B Square XBasis ZBasis) :
    QEC.Coding.BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile
      (max (Fintype.card A * Fintype.card B)
        (2 * Fintype.card XBasis + 2 * Fintype.card ZBasis)) := by sorry
