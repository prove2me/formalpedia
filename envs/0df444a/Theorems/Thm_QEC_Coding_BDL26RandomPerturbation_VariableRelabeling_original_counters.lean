-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_VariableRelabeling_original_counters
-- name    : QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.original_counters
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:18:32.250238+00:00
-- url     : https://prove2.me/theorems/08535dd9-a4c7-4ff0-9663-bff9e870f32d
-- title:
--   Variable Relabeling: original counters
-- statement:
--   The Variable Relabeling construction uses the original counters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/VariableRelabeling.lean#L56-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/VariableRelabeling.lean#L56-L61

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

theorem QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.original_counters (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P)
    (T : HTable (Vertex P) Space) (m : ℕ) (a : A) :
    counters (pulledSupport P J r u) (pulledBad P J r lambda K u) (encodeTable u T) m a=
      counters (eventSupport P J r) (eventBad P J r lambda K) T m (u a) := by sorry
