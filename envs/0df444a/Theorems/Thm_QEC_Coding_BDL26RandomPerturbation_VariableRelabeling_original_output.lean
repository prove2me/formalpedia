-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_VariableRelabeling_original_output
-- name    : QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.original_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:06:27.235252+00:00
-- url     : https://prove2.me/theorems/e18ded9a-f28e-4fa4-9ae3-2756d3766c08
-- title:
--   Variable Relabeling: original output
-- statement:
--   The Variable Relabeling construction uses the original output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/VariableRelabeling.lean#L79-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/VariableRelabeling.lean#L79-L83

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

theorem QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.original_output (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (T : HTable (Vertex P) Space) (a : A) :
    pulledOutput P J r lambda K u (encodeTable u T) a=
      output (eventSupport P J r) (eventBad P J r lambda K) T (u a) := by sorry
