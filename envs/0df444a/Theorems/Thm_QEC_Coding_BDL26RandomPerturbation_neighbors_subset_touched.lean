-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_neighbors_subset_touched
-- name    : QEC.Coding.BDL26RandomPerturbation.neighbors_subset_touched
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:05:27.537993+00:00
-- url     : https://prove2.me/theorems/a6009362-aa57-43c9-9438-ba71c8b8291d
-- title:
--   BDL26 Random Perturbation: neighbors subset touched
-- statement:
--   Every actual graph neighbor touches one of the event's actual support vertices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/DependencyCounts.lean#L73-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/DependencyCounts.lean#L73-L83

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.neighbors_subset_touched (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (e : Event P J K) :
    (supportGraph (eventSupport P J K)).neighborFinset e ⊆
      (eventSupport P J K e).biUnion (eventsAtVertex P J K) := by sorry
