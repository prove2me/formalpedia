-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_ChainComplexData_finiteQuditRowCheck_region_selected
-- name    : QEC.Coding.QuantumTanner.ChainComplexData.finiteQuditRowCheck_region_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:45:23.207854+00:00
-- url     : https://prove2.me/theorems/036490da-7f4c-4358-8ed9-513175886663
-- title:
--   Chain Complex Data: finite Qudit Row Check region selected
-- statement:
--   The selected region of a finite row check is exactly the check support in
--   the canonical chain-complex boundary incidence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9060-L9072
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L9060-L9072

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

theorem QEC.Coding.QuantumTanner.ChainComplexData.finiteQuditRowCheck_region_selected
    {iota kappa lambda : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) kappa) (Word (ZMod 2) iota)
        (Word (ZMod 2) lambda))
    (c : Sum kappa lambda) :
    (finiteQuditRowCheck K c).region.selected =
      (QEC.QLDPC.chainComplexBoundaryIncidence K).checkSupport c := by sorry
