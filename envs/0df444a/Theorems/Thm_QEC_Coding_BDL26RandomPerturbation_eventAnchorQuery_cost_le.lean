-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventAnchorQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.eventAnchorQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:13:23.985616+00:00
-- url     : https://prove2.me/theorems/706b0e1f-5981-4f44-9705-66540673874b
-- title:
--   BDL26 Random Perturbation: event Anchor Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the event Anchor Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L112-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/AnchorQuery.lean#L112-L122

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.eventAnchorQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) :
    (eventAnchorQuery P J r e).2 ≤ 8*Fintype.card (Triangle P)+9 := by sorry
