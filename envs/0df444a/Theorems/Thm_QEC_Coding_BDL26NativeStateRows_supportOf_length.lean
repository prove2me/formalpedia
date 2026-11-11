-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_supportOf_length
-- name    : QEC.Coding.BDL26NativeStateRows.supportOf_length
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:42:16.458477+00:00
-- url     : https://prove2.me/theorems/5f7f8a97-c420-4ee2-b125-feeb6ee0327a
-- title:
--   BDL26 Native State Rows: support Of length
-- statement:
--   The BDL26 Native State Rows construction uses the support Of length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L650-L656
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L650-L656

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
noncomputable section
open scoped Classical
open QEC.Coding.ProbabilisticConstruction

theorem QEC.Coding.BDL26NativeStateRows.supportOf_length (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r : ℝ) (e : Option (Event (P S n) J r)) : (supportOf S n J r e).length≤12 := by sorry
