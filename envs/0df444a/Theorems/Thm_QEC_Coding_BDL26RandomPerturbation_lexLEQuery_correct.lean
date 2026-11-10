-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lexLEQuery_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.lexLEQuery_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:11:12.280175+00:00
-- url     : https://prove2.me/theorems/bfedaf23-5ebd-499f-9754-5465c5abfe07
-- title:
--   BDL26 Random Perturbation: lex LEQuery correct
-- statement:
--   The BDL26 Random Perturbation construction uses the lex LEQuery correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L55-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventKeyQuery.lean#L55-L84

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Mathlib.Data.List.FinRange
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.lexLEQuery_correct (L M : List ℕ) : (lexLEQuery L M).1 = true ↔ L ≤ M := by sorry
