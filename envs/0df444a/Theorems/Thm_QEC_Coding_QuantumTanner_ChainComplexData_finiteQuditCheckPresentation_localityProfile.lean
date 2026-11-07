-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_ChainComplexData_finiteQuditCheckPresentation_localityProfile
-- name    : QEC.Coding.QuantumTanner.ChainComplexData.finiteQuditCheckPresentation_localityProfile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:28:39.625215+00:00
-- url     : https://prove2.me/theorems/19013ee1-4a83-42fa-b82b-c2862a3d66a2
-- title:
--   Chain Complex Data: finite Qudit Check Presentation locality Profile
-- statement:
--   Consequently the presentation's semantic locality profile is exactly the
--   already bounded boundary-incidence locality profile.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9165-L9180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9165-L9180

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
open QEC.Coding.QuantumTanner.ChainComplexData

theorem QEC.Coding.QuantumTanner.ChainComplexData.finiteQuditCheckPresentation_localityProfile
    {iota kappa lambda : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) kappa) (Word (ZMod 2) iota)
        (Word (ZMod 2) lambda))
    (encodedQudits : Nat)
    (hdimension :
      Module.finrank Complex (K.binaryCSSCode).stabilizer.code.carrier =
        2 ^ encodedQudits) :
    (finiteQuditCheckPresentation K encodedQudits hdimension).localityProfile =
      (QEC.QLDPC.chainComplexBoundaryIncidence K).localityProfile := by sorry
