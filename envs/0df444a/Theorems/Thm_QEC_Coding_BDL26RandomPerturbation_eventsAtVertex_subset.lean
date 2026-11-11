-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventsAtVertex_subset
-- name    : QEC.Coding.BDL26RandomPerturbation.eventsAtVertex_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:04:26.107807+00:00
-- url     : https://prove2.me/theorems/d626c273-cd85-4664-b0a1-7d71a808aea4
-- title:
--   BDL26 Random Perturbation: events At Vertex subset
-- statement:
--   The BDL26 Random Perturbation construction uses the events At Vertex subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/DependencyCounts.lean#L46-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/DependencyCounts.lean#L46-L55

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventsAtVertex_subset (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (v : Vertex P) :
    eventsAtVertex P J K v ⊆ (incidentTriangles P v).biUnion (eventsAtTriangle P J K) := by sorry
