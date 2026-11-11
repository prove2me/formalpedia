-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_VariableRelabeling_original_joint_law
-- name    : QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.original_joint_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:43:21.451374+00:00
-- url     : https://prove2.me/theorems/b2e198ac-a5b9-4ce4-95ed-1d908c69bdf0
-- title:
--   Variable Relabeling: original joint law
-- statement:
--   Native pulled laws give the complete joint law, no output-marginal substitution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/VariableRelabeling.lean#L157-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/VariableRelabeling.lean#L157-L167

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

theorem QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.original_joint_law (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (R c : ℝ) (hc : c<1) (u : A ≃ Vertex P) :
    letI (v : Vertex P) := vertexLaw_probability P R hc v
    letI (a : A) := pulledVertexLaw_probability P R c hc u a
    (tableLaw (pulledVertexLaw P R c u)).map
      (decodedObservation u (eventSupport P J r) (eventBad P J r lambda K))=
      (tableLaw (vertexLaw P R c)).map
        (jointObservation (eventSupport P J r) (eventBad P J r lambda K)) := by sorry
