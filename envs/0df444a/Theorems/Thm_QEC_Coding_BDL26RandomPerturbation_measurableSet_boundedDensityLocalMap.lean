-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_boundedDensityLocalMap
-- name    : QEC.Coding.BDL26RandomPerturbation.measurableSet_boundedDensityLocalMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:36:05.873101+00:00
-- url     : https://prove2.me/theorems/7e98e30e-d7f0-4fd6-a9e4-ffef72a540a1
-- title:
--   BDL26 Random Perturbation: measurable Set bounded Density Local Map
-- statement:
--   The exact original all-centre, multiplicity-preserving input/output domain is Borel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodMapMeasurability.lean#L153-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodMapMeasurability.lean#L153-L181

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set

theorem QEC.Coding.BDL26RandomPerturbation.measurableSet_boundedDensityLocalMap (P : TannerSquarePresentation) (t : ℝ) :
    MeasurableSet {J : Vertex P → Space | IsBoundedDensityLocalMap P J t} := by sorry
