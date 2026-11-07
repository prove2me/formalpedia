-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_finiteQuditCheckPresentation_localityProfile
-- name    : QEC.Coding.QuantumTanner.Data.finiteQuditCheckPresentation_localityProfile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:50:28.478447+00:00
-- url     : https://prove2.me/theorems/48ee8100-68b5-464f-b168-685106fd4068
-- title:
--   Data: finite Qudit Check Presentation locality Profile
-- statement:
--   The local-check presentation retains exactly the boundary-row incidence
--   used by the construction-owned locality estimates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9720-L9726
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9720-L9726

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
variable [DecidableEq Square]

theorem QEC.Coding.QuantumTanner.Data.finiteQuditCheckPresentation_localityProfile
    (D : Data G A B Square XBasis ZBasis) :
    D.finiteQuditCheckPresentation.localityProfile =
      (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile := by sorry
