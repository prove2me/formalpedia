-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_constrainedEdges_filter
-- name    : QEC.Coding.FiberBundle.RandomBase.constrainedEdges_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:46:55.2282+00:00
-- url     : https://prove2.me/theorems/62418363-ce87-485f-9ff6-560aa35173d9
-- title:
--   Random Base: constrained Edges filter
-- statement:
--   The constrained edge set is the Cartesian product `S × (univ \ T)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L430-L437
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L430-L437

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.constrainedEdges_filter
    {r : Nat} (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    (Finset.univ.filter fun edge : Fin (3 * r) × Fin (4 * r) =>
      edge.1 ∈ S ∧ edge.2 ∉ T) =
      S ×ˢ ((Finset.univ : Finset (Fin (4 * r))) \ T) := by sorry
