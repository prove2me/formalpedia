-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_isClosed_faceBallHit
-- name    : QEC.Coding.BDL26RandomPerturbation.isClosed_faceBallHit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:07:33.228206+00:00
-- url     : https://prove2.me/theorems/2284daa4-1ba2-488e-85fa-4474298c145b
-- title:
--   BDL26 Random Perturbation: is Closed face Ball Hit
-- statement:
--   The BDL26 Random Perturbation construction uses the is Closed face Ball Hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodMapMeasurability.lean#L28-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodMapMeasurability.lean#L28-L84

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set

theorem QEC.Coding.BDL26RandomPerturbation.isClosed_faceBallHit (P : TannerSquarePresentation) (f : P.Face) :
    IsClosed {z : (Vertex P → Space) × Space | faceBallHit P z.1 f z.2} := by sorry
