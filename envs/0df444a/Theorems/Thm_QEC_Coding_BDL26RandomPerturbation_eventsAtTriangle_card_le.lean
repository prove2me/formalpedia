-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventsAtTriangle_card_le
-- name    : QEC.Coding.BDL26RandomPerturbation.eventsAtTriangle_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:04:15.373422+00:00
-- url     : https://prove2.me/theorems/9f71ea93-ac1a-4286-8a1c-203607fa2ea9
-- title:
--   BDL26 Random Perturbation: events At Triangle card le
-- statement:
--   Erasing the fixed label injects four-triangle events into local three-element subsets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/DependencyCounts.lean#L21-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/DependencyCounts.lean#L21-L44

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventsAtTriangle_card_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K M : ℕ) (a : Triangle P) (hpool : (localPool P J K a).card ≤ M) :
    (eventsAtTriangle P J K a).card ≤ M^3 := by sorry
