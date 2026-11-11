-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_VariableRelabeling_pulled_table_law
-- name    : QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.pulled_table_law
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:21:22.587221+00:00
-- url     : https://prove2.me/theorems/37e9ed31-0ba5-4f8e-bab8-ce700e4dc92f
-- title:
--   Variable Relabeling: pulled table law
-- statement:
--   Current native original cap coordinates reindex without changing Nat columns.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/VariableRelabeling.lean#L135-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/VariableRelabeling.lean#L135-L142

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

theorem QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.pulled_table_law (P : TannerSquarePresentation) (R c : ℝ) (hc : c<1)
    (u : A ≃ Vertex P) :
    letI (v : Vertex P) := vertexLaw_probability P R hc v
    letI (a : A) := pulledVertexLaw_probability P R c hc u a
    (tableLaw (vertexLaw P R c)).map (encodeTable u)=tableLaw (pulledVertexLaw P R c u) := by sorry
