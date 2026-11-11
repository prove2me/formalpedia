-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometric_output_support_ae
-- name    : QEC.Coding.BDL26RandomPerturbation.geometric_output_support_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:49:11.211362+00:00
-- url     : https://prove2.me/theorems/1960d72e-e6ec-46c9-8953-d0e21ea586b5
-- title:
--   BDL26 Random Perturbation: geometric output support ae
-- statement:
--   The BDL26 Random Perturbation construction uses the geometric output support ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Execution.lean#L85-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Execution.lean#L85-L99

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPriority
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.geometric_output_support_ae (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) :
    letI (v : Vertex P) := vertexLaw_probability P
      ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
    ∀ᵐ T ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)),
      geometricOutput P J p T ∈ geometricSupport P p := by sorry
