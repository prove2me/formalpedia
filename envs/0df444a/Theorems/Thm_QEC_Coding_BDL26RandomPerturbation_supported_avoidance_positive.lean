-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_supported_avoidance_positive
-- name    : QEC.Coding.BDL26RandomPerturbation.supported_avoidance_positive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:18:45.009601+00:00
-- url     : https://prove2.me/theorems/19ecc5f4-b90a-4790-b801-9b0060901db8
-- title:
--   BDL26 Random Perturbation: supported avoidance positive
-- statement:
--   Intersecting with the cap-supported assignments preserves all positive avoidance mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodAssignments.lean#L48-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodAssignments.lean#L48-L55

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AvoidanceDensity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.supported_avoidance_positive (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    0 < (geometricLaw P p).real (geometricSupport P p ∩ geometricAvoidance P J p) := by sorry
