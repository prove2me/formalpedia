-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_read_first
-- name    : QEC.Coding.BDL26NativeStateRows.read_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:43:24.700843+00:00
-- url     : https://prove2.me/theorems/fa7d329b-506e-4e96-bbf7-5fa59d288dad
-- title:
--   BDL26 Native State Rows: read first
-- statement:
--   The BDL26 Native State Rows construction uses the read first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L253-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L253-L254

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

theorem QEC.Coding.BDL26NativeStateRows.read_first {A : Type*} [DecidableEq A] (a : A) (k : ℕ) (x : Space)
    (R : Rows A) : (readQ a ((a,k,x)::R)).value=(k,x) := by sorry
