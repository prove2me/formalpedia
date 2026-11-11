-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometric_output_density_ae
-- name    : QEC.Coding.BDL26RandomPerturbation.geometric_output_density_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:17:26.136738+00:00
-- url     : https://prove2.me/theorems/2620ece5-abee-40f8-a550-8be719dcb499
-- title:
--   BDL26 Random Perturbation: geometric output density ae
-- statement:
--   The BDL26 Random Perturbation construction uses the geometric output density ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Execution.lean#L117-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Execution.lean#L117-L131

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

theorem QEC.Coding.BDL26RandomPerturbation.geometric_output_density_ae (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    letI (v : Vertex P) := vertexLaw_probability P
      ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
    ∀ᵐ T ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)),
      ∀ z, ((familyHits (oldTriangleImage P
        (perturbedMap P J p.lambda (geometricOutput P J p T)))
          (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by sorry
