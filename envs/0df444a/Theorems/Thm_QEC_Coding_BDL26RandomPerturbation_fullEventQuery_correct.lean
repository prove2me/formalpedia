-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fullEventQuery_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.fullEventQuery_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:14:57.411238+00:00
-- url     : https://prove2.me/theorems/ad6f1bfd-04a4-4e1f-a6cd-fc47b4d1cd86
-- title:
--   BDL26 Random Perturbation: full Event Query correct
-- statement:
--   The BDL26 Random Perturbation construction uses the full Event Query correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FullEventQuery.lean#L75-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FullEventQuery.lean#L75-L83

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SnapshotQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.fullEventQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (p : eventSupport P J r e → Space) :
    (fullEventQuery P J r lambda K e p).1 = true ↔ p ∈ eventBad P J r lambda K e := by sorry
