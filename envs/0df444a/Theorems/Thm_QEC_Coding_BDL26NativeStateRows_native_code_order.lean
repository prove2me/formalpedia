-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_native_code_order
-- name    : QEC.Coding.BDL26NativeStateRows.native_code_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:47:44.713893+00:00
-- url     : https://prove2.me/theorems/865866ec-544a-4f22-bfb4-e1e695f4cb01
-- title:
--   BDL26 Native State Rows: native code order
-- statement:
--   The BDL26 Native State Rows construction uses the native code order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L573-L578
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L573-L578

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

theorem QEC.Coding.BDL26NativeStateRows.native_code_order (S : OddScale) (n : ℕ) (T : Samples (Index S n)) :
    ((initializeQ S n T).value.map Prod.fst).map
        (BDL26NativePresentationGenerator.setupQ S n).1.data.vertices.get=
      (BDL26NativePresentationGenerator.setupQ S n).1.data.vertices := by sorry
