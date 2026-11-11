-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_isClosed_boundedLabelHit
-- name    : QEC.Coding.BDL26RandomPerturbation.isClosed_boundedLabelHit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:09:44.39299+00:00
-- url     : https://prove2.me/theorems/394aa980-d34b-4e8e-b665-c49b339bf561
-- title:
--   BDL26 Random Perturbation: is Closed bounded Label Hit
-- statement:
--   The BDL26 Random Perturbation construction uses the is Closed bounded Label Hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodMapMeasurability.lean#L91-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodMapMeasurability.lean#L91-L117

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set

theorem QEC.Coding.BDL26RandomPerturbation.isClosed_boundedLabelHit (P : TannerSquarePresentation) (s : Finset P.Face)
    (N : ℕ) : IsClosed (boundedLabelHit P s N) := by sorry
