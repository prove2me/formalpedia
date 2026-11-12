-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_asTable_read
-- name    : QEC.Coding.BDL26NativeStateRows.asTable_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:43:22.727905+00:00
-- url     : https://prove2.me/theorems/dec71dc4-c70e-4e2c-aeb3-b255e84e4b80
-- title:
--   BDL26 Native State Rows: as Table read
-- statement:
--   The BDL26 Native State Rows construction uses the as Table read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L201-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L201-L202

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

theorem QEC.Coding.BDL26NativeStateRows.asTable_read {A : Type*} (T : Samples A) (a : A) (k : ℕ) :
    asTable T (a,k)=T (a,k) := by sorry
