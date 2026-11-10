-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lexLEQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.lexLEQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:10:38.96078+00:00
-- url     : https://prove2.me/theorems/8f221447-249b-4eb2-8953-64c6326cea38
-- title:
--   BDL26 Random Perturbation: lex LEQuery cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the lex LEQuery cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L86-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L86-L95

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Mathlib.Data.List.FinRange
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.lexLEQuery_cost_le (L M : List ℕ) : (lexLEQuery L M).2 ≤ 2*L.length+1 := by sorry
