-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_mem_couniqueNeighbors_iff_exists_unique
-- name    : QEC.Coding.FiberBundle.RandomBase.mem_couniqueNeighbors_iff_exists_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:53:02.027303+00:00
-- url     : https://prove2.me/theorems/84a8f384-4706-4a7d-9185-31566b914591
-- title:
--   Random Base: mem counique Neighbors iff exists unique
-- statement:
--   Membership in the counique-neighbor set means that exactly one selected check
--   is incident to the variable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L45-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L45-L84

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.mem_couniqueNeighbors_iff_exists_unique
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) (b : Fin (4 * r)) :
    b ∈ couniqueNeighbors sample S ↔
      ∃ a ∈ S,
        sample (a, b) = true ∧
          ∀ a' ∈ S, sample (a', b) = true → a' = a := by sorry
