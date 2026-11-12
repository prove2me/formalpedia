-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_VariableRelabeling_original_nonhalting_output
-- name    : QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.original_nonhalting_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:22:48.781963+00:00
-- url     : https://prove2.me/theorems/a861dafe-d646-4dc1-94e7-6df6b08a37a0
-- title:
--   Variable Relabeling: original nonhalting output
-- statement:
--   The Variable Relabeling construction uses the original nonhalting output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/VariableRelabeling.lean#L104-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/VariableRelabeling.lean#L104-L108

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding BDL26DecodingGraph
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.original_nonhalting_output (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (T : HTable (Vertex P) Space)
    (h : ¬Halts (eventSupport P J r) (eventBad P J r lambda K) T) :
    pulledOutput P J r lambda K u (encodeTable u T)=fun a => T (u a,0) := by sorry
