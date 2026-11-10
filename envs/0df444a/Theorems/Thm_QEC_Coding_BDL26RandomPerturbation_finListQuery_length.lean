-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_finListQuery_length
-- name    : QEC.Coding.BDL26RandomPerturbation.finListQuery_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:08:15.199082+00:00
-- url     : https://prove2.me/theorems/bb129c96-3ab4-40ca-afe3-74d7719077e4
-- title:
--   BDL26 Random Perturbation: fin List Query length
-- statement:
--   The BDL26 Random Perturbation construction uses the fin List Query length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L15-L16
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridEnumerationQuery.lean#L15-L16

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation

theorem QEC.Coding.BDL26RandomPerturbation.finListQuery_length (n : ℕ) : (finListQuery n).1.length = n := by sorry
