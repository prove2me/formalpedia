-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actual_event_criterion
-- name    : QEC.Coding.BDL26RandomPerturbation.actual_event_criterion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:09:58.685211+00:00
-- url     : https://prove2.me/theorems/84b47733-e806-4351-88b9-3c32af5b5e65
-- title:
--   BDL26 Random Perturbation: actual event criterion
-- statement:
--   The BDL26 Random Perturbation construction uses the actual event criterion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalLemmaApplication.lean#L11-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalLemmaApplication.lean#L11-L29

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalLemmaApplication
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.actual_event_criterion (P : TannerSquarePresentation) (J : Vertex P → Space)
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P)
    (e : Event P J (anchorRadius p.m)) :
    (Measure.pi (vertexLaw P ((6*p.m : ℕ)* (p.lambda : ℝ)) (capCutoff p.m))).real
      (localEvent (eventSupport P J (anchorRadius p.m))
        (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      lllWeight (dependencyBound p.M)*
        ∏ _j ∈ (supportGraph (eventSupport P J (anchorRadius p.m))).neighborFinset e,
          (1-lllWeight (dependencyBound p.M)) := by sorry
