-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fiberRankQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.fiberRankQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:53:49.651632+00:00
-- url     : https://prove2.me/theorems/dce9f4f5-2c2b-4aaa-a69b-a2d7e8509da2
-- title:
--   BDL26 Random Perturbation: fiber Rank Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the fiber Rank Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ColorQuery.lean#L65-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ColorQuery.lean#L65-L75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare

theorem QEC.Coding.BDL26RandomPerturbation.fiberRankQuery_value (P : TannerSquarePresentation) {A : Type*} [DecidableEq A]
    (f : Triangle P → A) (a : Triangle P) :
    (fiberRankQuery P f a).1 = fiberRank (triangleKey P) f a := by sorry
