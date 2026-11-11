-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_localPool_subset_hits
-- name    : QEC.Coding.BDL26RandomPerturbation.localPool_subset_hits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:04:37.48507+00:00
-- url     : https://prove2.me/theorems/30075172-7e61-47c8-ae50-2bdd7822f093
-- title:
--   BDL26 Random Perturbation: local Pool subset hits
-- statement:
--   The BDL26 Random Perturbation construction uses the local Pool subset hits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L56-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean#L56-L65

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.localPool_subset_hits (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (a : Triangle P) :
    localPool P J K a ⊆ familyHits (oldTriangleImage P (fun v => (1/2 : ℝ) • J v))
      (Metric.closedBall (oldAnchor P J a) K) := by sorry
