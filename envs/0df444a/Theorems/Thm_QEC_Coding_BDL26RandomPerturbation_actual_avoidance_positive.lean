-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actual_avoidance_positive
-- name    : QEC.Coding.BDL26RandomPerturbation.actual_avoidance_positive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:04:54.296201+00:00
-- url     : https://prove2.me/theorems/2868b055-8645-4635-abc5-e19993fd6ba5
-- title:
--   BDL26 Random Perturbation: actual avoidance positive
-- statement:
--   The actual continuous product law gives positive mass to simultaneous avoidance.
--   All dependency and probability hypotheses are derived from the incoming density and valence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalLemmaApplication.lean#L33-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalLemmaApplication.lean#L33-L51

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalLemmaApplication
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.actual_avoidance_positive (P : TannerSquarePresentation) (J : Vertex P → Space)
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    0 < (Measure.pi (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))).real
      (avoid (localEvent (eventSupport P J (anchorRadius p.m))
        (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))) Finset.univ) := by sorry
