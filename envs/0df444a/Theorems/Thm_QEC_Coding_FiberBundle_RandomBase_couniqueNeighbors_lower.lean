-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_couniqueNeighbors_lower
-- name    : QEC.Coding.FiberBundle.RandomBase.couniqueNeighbors_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:47:02.770503+00:00
-- url     : https://prove2.me/theorems/ad1e68d9-db9c-4126-b1e5-25bfbdb9526d
-- title:
--   Random Base: counique Neighbors lower
-- statement:
--   At least `0.83 Delta |S|` neighbors are counique.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L264-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L264-L276

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.couniqueNeighbors_lower
    {r Delta : Nat} {sample : Sample r}
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (hExpansion : HasStrongSmallSetExpansion (Delta := Delta) sample)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    83 * Delta * S.card ≤
      100 * (couniqueNeighbors sample S).card := by sorry
