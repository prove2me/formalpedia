-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_read_cost
-- name    : QEC.Coding.BDL26NativeStateRows.read_cost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:41:44.754702+00:00
-- url     : https://prove2.me/theorems/34c59629-3adb-470f-8c78-9d94b258ff74
-- title:
--   BDL26 Native State Rows: read cost
-- statement:
--   The BDL26 Native State Rows construction uses the read cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L269-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L269-L278

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

theorem QEC.Coding.BDL26NativeStateRows.read_cost {A : Type*} [DecidableEq A] (a : A) (R : Rows A) :
    (readQ a R).operations≤2*R.length+1 ∧ (readQ a R).allocations=0 := by sorry
