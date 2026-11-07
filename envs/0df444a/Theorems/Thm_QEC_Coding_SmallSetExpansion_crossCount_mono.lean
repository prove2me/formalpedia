-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_mono
-- name    : QEC.Coding.SmallSetExpansion.crossCount_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:46:01.802355+00:00
-- url     : https://prove2.me/theorems/93890603-c0b1-4e2a-892d-64e81eda3791
-- title:
--   Small Set Expansion: cross Count mono
-- statement:
--   Pointwise domination of weighted graphs increases every cross count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L245-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L245-L251

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.crossCount_mono
    {M N : WeightedGraph V} (hMN : ∀ v u, M v u ≤ N v u)
    (S T : Finset V) :
    crossCount M S T ≤ crossCount N S T := by sorry
