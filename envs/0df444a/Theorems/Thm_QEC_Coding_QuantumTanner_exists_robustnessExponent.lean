-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_robustnessExponent
-- name    : QEC.Coding.QuantumTanner.exists_robustnessExponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:01:10.317269+00:00
-- url     : https://prove2.me/theorems/222d286c-7e5a-4247-8ca0-2460e104c55a
-- title:
--   Quantum Tanner: exists robustness Exponent
-- statement:
--   Every exponent `epsilon` in the range used by LZ22 admits the auxiliary
--   robustness exponent `gamma` required in Theorem `thm:P-robust`.  The explicit
--   midpoint choice keeps the strict source inequalities visible for the later
--   probabilistic robustness argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L107-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L107-L113

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

theorem QEC.Coding.QuantumTanner.exists_robustnessExponent
    {epsilon : ℝ} (_hEpsilonPositive : 0 < epsilon)
    (hEpsilonHalf : epsilon < 1 / 2) :
    ∃ gamma : ℝ, 1 / 2 + epsilon < gamma ∧ gamma < 1 := by sorry
