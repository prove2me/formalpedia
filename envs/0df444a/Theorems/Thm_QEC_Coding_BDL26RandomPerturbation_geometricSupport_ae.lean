-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricSupport_ae
-- name    : QEC.Coding.BDL26RandomPerturbation.geometricSupport_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:18:22.131286+00:00
-- url     : https://prove2.me/theorems/ee57e80c-7fee-4a1b-822b-029a808de2d5
-- title:
--   BDL26 Random Perturbation: geometric Support ae
-- statement:
--   The BDL26 Random Perturbation construction uses the geometric Support ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodAssignments.lean#L36-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodAssignments.lean#L36-L45

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AvoidanceDensity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.geometricSupport_ae (P : TannerSquarePresentation) {L : ℝ}
    (p : GeometricParameters L) : ∀ᵐ w ∂geometricLaw P p, w ∈ geometricSupport P p := by sorry
