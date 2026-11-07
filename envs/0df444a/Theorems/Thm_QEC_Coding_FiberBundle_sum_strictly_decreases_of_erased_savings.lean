-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_sum_strictly_decreases_of_erased_savings
-- name    : QEC.Coding.FiberBundle.sum_strictly_decreases_of_erased_savings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:03:01.907374+00:00
-- url     : https://prove2.me/theorems/807a1b85-718a-449c-8e0a-b07e6e8252d8
-- title:
--   Fiber Bundle: sum strictly decreases of erased savings
-- statement:
--   Finite-sum descent principle used by the `> 4/5` counique argument: the erased
--   set contributes a fixed positive saving, while all remaining coordinates pay
--   strictly less total correction cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1480-L1524
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1480-L1524

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.sum_strictly_decreases_of_erased_savings
    {β : Type u} [Fintype β] [DecidableEq β]
    (C : Finset β) (old new cost : β → Nat) (w : Nat)
    (hNewZero : ∀ b ∈ C, new b = 0)
    (hOldWeight : ∀ b ∈ C, old b = w)
    (hOutside : ∀ b ∈ (Finset.univ \ C), new b ≤ old b + cost b)
    (hCost :
      (∑ b ∈ (Finset.univ \ C), cost b) < C.card * w) :
    (∑ b : β, new b) < ∑ b : β, old b := by sorry
