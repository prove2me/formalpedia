-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_constrainedEdges
-- name    : QEC.Coding.FiberBundle.RandomBase.card_constrainedEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:46:27.576371+00:00
-- url     : https://prove2.me/theorems/ce6c7912-a7c6-42ba-949f-11bb3bfba5a9
-- title:
--   Random Base: card constrained Edges
-- statement:
--   Exact number of constrained incidences from `S` to outside `T`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L440-L447
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L440-L447

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.card_constrainedEdges
    {r : Nat} (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    (Finset.univ.filter fun edge : Fin (3 * r) × Fin (4 * r) =>
      edge.1 ∈ S ∧ edge.2 ∉ T).card =
      S.card * (4 * r - T.card) := by sorry
