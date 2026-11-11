-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_native_length_bound
-- name    : QEC.Coding.BDL26NativeStateRows.native_length_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:51:05.621501+00:00
-- url     : https://prove2.me/theorems/cc7159cd-91d3-4fdf-a974-93dd7d377eea
-- title:
--   BDL26 Native State Rows: native length bound
-- statement:
--   The retained input record bound ties cache length to the actual accepted
--   generator polynomial, rather than a supplied list-cardinality budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L566-L571
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L566-L571

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeStateRows
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem QEC.Coding.BDL26NativeStateRows.native_length_bound (S : OddScale) (n : ℕ) :
    count S n≤(n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15 := by sorry
