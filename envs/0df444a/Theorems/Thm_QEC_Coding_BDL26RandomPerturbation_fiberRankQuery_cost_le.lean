-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fiberRankQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.fiberRankQuery_cost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:53:16.760552+00:00
-- url     : https://prove2.me/theorems/355951d2-5fa9-478f-afa1-26ec07605edd
-- title:
--   BDL26 Random Perturbation: fiber Rank Query cost le
-- statement:
--   Both ranks are derived by finite input lookup; two owner reads and both comparisons are counted.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ColorQuery.lean#L36-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ColorQuery.lean#L36-L50

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare

theorem QEC.Coding.BDL26RandomPerturbation.fiberRankQuery_cost_le (P : TannerSquarePresentation) {A : Type*} [DecidableEq A]
    (f : Triangle P → A) (a : Triangle P) :
    (fiberRankQuery P f a).2 ≤ Fintype.card (Triangle P)*(Fintype.card (Triangle P)+6) := by sorry
