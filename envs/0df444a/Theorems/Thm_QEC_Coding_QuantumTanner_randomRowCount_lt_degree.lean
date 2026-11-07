-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_randomRowCount_lt_degree
-- name    : QEC.Coding.QuantumTanner.randomRowCount_lt_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:25:26.161987+00:00
-- url     : https://prove2.me/theorems/88adb330-704a-480c-9f85-91795e6b88a6
-- title:
--   Quantum Tanner: random Row Count lt degree
-- statement:
--   At a nonempty degree and a source rate strictly below one, the random
--   matrix has fewer rows than columns.  In particular this supplies the
--   `r ≤ Delta` side condition used by the exact `Delta²` locality estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L80-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L80-L90

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

theorem QEC.Coding.QuantumTanner.randomRowCount_lt_degree
    {rho : ℝ} {Delta : Nat} (hRhoNonnegative : 0 ≤ rho)
    (hRhoOne : rho < 1) (hDelta : 0 < Delta) :
    randomRowCount rho Delta < Delta := by sorry
