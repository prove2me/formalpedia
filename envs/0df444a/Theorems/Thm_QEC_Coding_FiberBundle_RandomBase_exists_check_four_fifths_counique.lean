-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_check_four_fifths_counique
-- name    : QEC.Coding.FiberBundle.RandomBase.exists_check_four_fifths_counique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:53:03.082529+00:00
-- url     : https://prove2.me/theorems/791833b2-7de3-44af-922c-fced3b9913cb
-- title:
--   Random Base: exists check four fifths counique
-- statement:
--   The selected check from the preceding lemma has a strict `4/5` counique
--   fraction of its whole neighborhood.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L357-L372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L357-L372

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.exists_check_four_fifths_counique
    {r Delta : Nat} {sample : Sample r}
    (hDelta : 0 < Delta)
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (hExpansion : HasStrongSmallSetExpansion (Delta := Delta) sample)
    (S : Finset (Fin (3 * r))) (hS : S.Nonempty)
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    ∃ a ∈ S,
      4 * checkDegree sample a < 5 * couniqueDegree sample S a := by sorry
