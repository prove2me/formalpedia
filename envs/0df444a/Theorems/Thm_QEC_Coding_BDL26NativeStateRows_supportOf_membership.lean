-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_supportOf_membership
-- name    : QEC.Coding.BDL26NativeStateRows.supportOf_membership
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:43:20.451226+00:00
-- url     : https://prove2.me/theorems/4e2e30f8-ec9b-45e3-a0b4-796c1edde741
-- title:
--   BDL26 Native State Rows: support Of membership
-- statement:
--   The BDL26 Native State Rows construction uses the support Of membership property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L639-L648
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L639-L648

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

theorem QEC.Coding.BDL26NativeStateRows.supportOf_membership (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r : ℝ) (e : Event (P S n) J r) (a : Index S n) :
    a∈supportOf S n J r (some e) ↔ decode S n a∈eventSupport (P S n) J r e := by sorry
