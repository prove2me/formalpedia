-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_countQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.countQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:52:55.719121+00:00
-- url     : https://prove2.me/theorems/a673aff5-e189-464f-a1a7-0cd72053a536
-- title:
--   BDL26 Random Perturbation: count Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the count Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ColorQuery.lean#L17-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ColorQuery.lean#L17-L25

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare

theorem QEC.Coding.BDL26RandomPerturbation.countQuery_cost_le {A : Type*} (q : A → Bool × ℕ) (L : List A) (C : ℕ)
    (hq : ∀ a ∈ L, (q a).2 ≤ C) : (countQuery q L).2 ≤ L.length*(C+1) := by sorry
