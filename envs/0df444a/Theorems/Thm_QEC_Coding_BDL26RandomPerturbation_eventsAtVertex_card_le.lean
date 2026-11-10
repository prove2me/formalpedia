-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventsAtVertex_card_le
-- name    : QEC.Coding.BDL26RandomPerturbation.eventsAtVertex_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:05:14.040048+00:00
-- url     : https://prove2.me/theorems/a97b8707-aa42-4608-9c1d-11f0af301b8c
-- title:
--   BDL26 Random Perturbation: events At Vertex card le
-- statement:
--   A touched vertex chooses at most 56 incident triangles, then at most M^3 events.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/DependencyCounts.lean#L58-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/DependencyCounts.lean#L58-L70

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventsAtVertex_card_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K M : ℕ) (hv : BoundedValence P)
    (hpool : ∀ a, (localPool P J K a).card ≤ M) (v : Vertex P) :
    (eventsAtVertex P J K v).card ≤ 56*M^3 := by sorry
