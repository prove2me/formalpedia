-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_member_cost
-- name    : QEC.Coding.BDL26NativeStateRows.member_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:49:49.498223+00:00
-- url     : https://prove2.me/theorems/d8af6e82-42b2-4977-8511-a44b13dfdb54
-- title:
--   BDL26 Native State Rows: member cost
-- statement:
--   The BDL26 Native State Rows construction uses the member cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L303-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L303-L312

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

theorem QEC.Coding.BDL26NativeStateRows.member_cost {A : Type*} [DecidableEq A] (a : A) (L : List A) :
    (memberQ a L).operations≤2*L.length+1 ∧ (memberQ a L).allocations=0 := by sorry
