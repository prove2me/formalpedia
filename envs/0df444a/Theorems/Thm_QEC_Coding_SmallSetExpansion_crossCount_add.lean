-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_add
-- name    : QEC.Coding.SmallSetExpansion.crossCount_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:51.505209+00:00
-- url     : https://prove2.me/theorems/ecab951c-437c-44d4-8ef0-3961e6633045
-- title:
--   Small Set Expansion: cross Count add
-- statement:
--   Cross counts are additive under weighted-graph union.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L86-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L86-L88

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.crossCount_add (M N : WeightedGraph V) (S T : Finset V) :
    crossCount (add M N) S T = crossCount M S T + crossCount N S T := by sorry
