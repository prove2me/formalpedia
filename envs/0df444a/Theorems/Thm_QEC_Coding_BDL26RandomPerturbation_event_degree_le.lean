-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_event_degree_le
-- name    : QEC.Coding.BDL26RandomPerturbation.event_degree_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:04:47.818359+00:00
-- url     : https://prove2.me/theorems/4ba2dca5-77cf-4b41-800e-cd3321b7aa83
-- title:
--   BDL26 Random Perturbation: event degree le
-- statement:
--   The derived degree bound contains no perturbation scale or global input size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/DependencyCounts.lean#L86-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/DependencyCounts.lean#L86-L100

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.event_degree_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K M : ℕ)
    (hv : BoundedValence P) (hpool : ∀ a, (localPool P J K a).card ≤ M)
    (e : Event P J K) :
    ((supportGraph (eventSupport P J K)).neighborFinset e).card ≤ 12*56*M^3 := by sorry
