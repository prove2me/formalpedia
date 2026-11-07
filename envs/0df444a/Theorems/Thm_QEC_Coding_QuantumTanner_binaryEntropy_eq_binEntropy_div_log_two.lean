-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_binaryEntropy_eq_binEntropy_div_log_two
-- name    : QEC.Coding.QuantumTanner.binaryEntropy_eq_binEntropy_div_log_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:39:38.675364+00:00
-- url     : https://prove2.me/theorems/8aa8ff5d-f643-4320-aac5-addca8f29a77
-- title:
--   Quantum Tanner: binary Entropy eq bin Entropy div log two
-- statement:
--   The source's base-two entropy is Mathlib's binary entropy in nats divided
--   by `log 2`.  This lets the later Hamming-ball estimate use Mathlib's analytic
--   properties without changing the normalization in the public statement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L49-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L49-L52

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

theorem QEC.Coding.QuantumTanner.binaryEntropy_eq_binEntropy_div_log_two (delta : ℝ) :
    binaryEntropy delta = Real.binEntropy delta / Real.log 2 := by sorry
