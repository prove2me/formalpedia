-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_smallNonemptyCheckSet_of_not_hasStrongSmallSetExpansion
-- name    : QEC.Coding.FiberBundle.RandomBase.exists_smallNonemptyCheckSet_of_not_hasStrongSmallSetExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:26.605944+00:00
-- url     : https://prove2.me/theorems/81775840-27f3-457e-88b3-fed95c1dda40
-- title:
--   Random Base: exists small Nonempty Check Set of not has Strong Small Set Expansion
-- statement:
--   Every failed strong-expansion sample supplies a nonempty small check set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1159-L1173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1159-L1173

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.exists_smallNonemptyCheckSet_of_not_hasStrongSmallSetExpansion
    {r Delta : Nat} {sample : Sample r}
    (h : ¬HasStrongSmallSetExpansion (Delta := Delta) sample) :
    ∃ S : SmallNonemptyCheckSet r Delta,
      100 * (checkSetNeighborhood sample S.1.1).card <
        92 * Delta * S.1.1.card := by sorry
