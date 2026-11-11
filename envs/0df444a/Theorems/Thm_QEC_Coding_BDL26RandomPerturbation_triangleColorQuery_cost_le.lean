-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleColorQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleColorQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:54:11.168368+00:00
-- url     : https://prove2.me/theorems/28425a59-c7d2-40a0-94a3-97137f74c351
-- title:
--   BDL26 Random Perturbation: triangle Color Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle Color Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ColorQuery.lean#L91-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ColorQuery.lean#L91-L98

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare

theorem QEC.Coding.BDL26RandomPerturbation.triangleColorQuery_cost_le (P : TannerSquarePresentation) (a : Triangle P) :
    (triangleColorQuery P a).2 ≤ 3*Fintype.card (Triangle P)*(Fintype.card (Triangle P)+6) := by sorry
