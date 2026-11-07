-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_mono_sets
-- name    : QEC.Coding.SmallSetExpansion.crossCount_mono_sets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:32:38.803404+00:00
-- url     : https://prove2.me/theorems/ebb87d74-5a30-46d5-b099-2c81b3dcbf4c
-- title:
--   Small Set Expansion: cross Count mono sets
-- statement:
--   Cross counts are monotone in both selected vertex sets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L349-L361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L349-L361

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.crossCount_mono_sets [DecidableEq V]
    (M : WeightedGraph V) {S S' T T' : Finset V}
    (hS : S ⊆ S') (hT : T ⊆ T') :
    crossCount M S T ≤ crossCount M S' T' := by sorry
