-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_emit_value
-- name    : QEC.Coding.BDL26NativeStateRows.emit_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:26:26.767188+00:00
-- url     : https://prove2.me/theorems/2ea86f68-a69b-4fc1-9db8-270d9029d206
-- title:
--   BDL26 Native State Rows: emit value
-- statement:
--   The BDL26 Native State Rows construction uses the emit value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L445-L447
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L445-L447

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

theorem QEC.Coding.BDL26NativeStateRows.emit_value {A : Type*} (L : List A) (T : Samples A) (c : A → ℕ) :
    (emitQ (rowsFor L T c)).value=L.map (fun a => (a,T (a,c a))) := by sorry
