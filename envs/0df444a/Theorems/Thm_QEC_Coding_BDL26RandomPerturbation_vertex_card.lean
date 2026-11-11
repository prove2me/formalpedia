-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertex_card
-- name    : QEC.Coding.BDL26RandomPerturbation.vertex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:28:20.011727+00:00
-- url     : https://prove2.me/theorems/f46b4f6f-4f89-4489-bf6a-3031435390d9
-- title:
--   BDL26 Random Perturbation: vertex card
-- statement:
--   The BDL26 Random Perturbation construction uses the vertex card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExpectedOperationCost.lean#L71-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExpectedOperationCost.lean#L71-L74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.vertex_card (P : TannerSquarePresentation) :
    Fintype.card (Vertex P) = Fintype.card P.X+Fintype.card P.Q+Fintype.card P.Z := by sorry
