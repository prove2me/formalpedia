-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fullEventQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.fullEventQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:00:13.657924+00:00
-- url     : https://prove2.me/theorems/b54e8ff9-9a85-447f-9319-f551d317e9e2
-- title:
--   BDL26 Random Perturbation: full Event Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the full Event Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FullEventQuery.lean#L89-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FullEventQuery.lean#L89-L111

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SnapshotQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.fullEventQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (p : eventSupport P J r e → Space) :
    (fullEventQuery P J r lambda K e p).2 ≤ fullQueryBudget (Fintype.card (Triangle P)) K := by sorry
