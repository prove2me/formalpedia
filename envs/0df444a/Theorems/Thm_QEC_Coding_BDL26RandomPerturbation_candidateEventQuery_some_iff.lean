-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_candidateEventQuery_some_iff
-- name    : QEC.Coding.BDL26RandomPerturbation.candidateEventQuery_some_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:31:03.080585+00:00
-- url     : https://prove2.me/theorems/9ee871da-f024-47ae-a3e0-624baba193e7
-- title:
--   BDL26 Random Perturbation: candidate Event Query some iff
-- statement:
--   The BDL26 Random Perturbation construction uses the candidate Event Query some iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibleListQuery.lean#L81-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EligibleListQuery.lean#L81-L99

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibilityQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibleListQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.candidateEventQuery_some_iff (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) (e : Event P J r) :
    (candidateEventQuery P J hr L).1 = some e ↔ L.toFinset = e.val := by sorry
