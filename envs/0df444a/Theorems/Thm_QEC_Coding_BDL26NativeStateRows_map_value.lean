-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_map_value
-- name    : QEC.Coding.BDL26NativeStateRows.map_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:19:56.9632+00:00
-- url     : https://prove2.me/theorems/d602f825-9eb9-49bb-94fb-bfc3e2b36add
-- title:
--   BDL26 Native State Rows: map value
-- statement:
--   The BDL26 Native State Rows construction uses the map value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L40-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L40-L42

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

theorem QEC.Coding.BDL26NativeStateRows.map_value {A B : Type*} (f : A → Run B) (L : List A) :
    (mapQ f L).value=L.map (fun a => (f a).value) := by sorry
