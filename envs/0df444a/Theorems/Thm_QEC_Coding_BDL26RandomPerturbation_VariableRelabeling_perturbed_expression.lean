-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_VariableRelabeling_perturbed_expression
-- name    : QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.perturbed_expression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:21:57.060112+00:00
-- url     : https://prove2.me/theorems/3a65c834-b2ca-4540-861a-37bfdff0d815
-- title:
--   Variable Relabeling: perturbed expression
-- statement:
--   The literal original perturbation, not a new interpolation or coordinate law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/VariableRelabeling.lean#L123-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/VariableRelabeling.lean#L123-L132

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

theorem QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.perturbed_expression (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (u : A ≃ Vertex P)
    (T : HTable (Vertex P) Space) (a : A) :
    p.lambda • ((1/2 : ℝ) • (J ∘ u) a)+
      pulledOutput P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) u (encodeTable u T) a=
      perturbedMap P J p.lambda (geometricOutput P J p T) (u a) := by sorry
