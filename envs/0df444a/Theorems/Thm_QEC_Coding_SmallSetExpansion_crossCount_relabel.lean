-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_relabel
-- name    : QEC.Coding.SmallSetExpansion.crossCount_relabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:54.292372+00:00
-- url     : https://prove2.me/theorems/dfe3682c-53db-43f6-93ec-60cbe2a1bf5f
-- title:
--   Small Set Expansion: cross Count relabel
-- statement:
--   Relabelling preserves cross counts after transporting the two sets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L106-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L106-L112

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.crossCount_relabel
    {U : Type*} [DecidableEq V] [DecidableEq U]
    (e : V ≃ U) (M : WeightedGraph V) (S T : Finset U) :
    crossCount (relabel e M) S T =
      crossCount M (S.map e.symm.toEmbedding) (T.map e.symm.toEmbedding) := by sorry
