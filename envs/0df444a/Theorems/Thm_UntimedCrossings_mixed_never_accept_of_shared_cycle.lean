-- Prove2me | Theorems.Thm_UntimedCrossings_mixed_never_accept_of_shared_cycle
-- name    : UntimedCrossings.mixed_never_accept_of_shared_cycle
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T22:46:59.853435+00:00
-- url     : https://prove2.me/theorems/410793c8-3231-5d1f-a1c4-97ebeec186f1
-- title:
--   A shared loop in untimed crossing records prevents both mixed runs from accepting
-- statement:
--   Two deterministic runs from the same starting state may be observed for different finite durations. Suppose their untimed crossing records share a prefix in which the same destination occurs twice, ending at its second occurrence. Form the complementary mixed transition maps by selecting which original map acts on each side. If acceptance is absorbing for the original maps, both mixed runs reject at every horizon.
-- source:
--   A loop extension of the crossing-sequence splicing method, using full arrival states.

import Definitions.Def_UntimedEndpointExchange

open UntimedCrossings

theorem UntimedCrossings.mixed_never_accept_of_shared_cycle {S : Type*} (side accept : S → Bool)
    (A B M N : S → S) (z x : S) (TA TB : ℕ) (lead middle tailA tailB : List S)
    (recordA : untimedRecord side A z TA = ((lead ++ [x]) ++ (middle ++ [x])) ++ tailA)
    (recordB : untimedRecord side B z TB = ((lead ++ [x]) ++ (middle ++ [x])) ++ tailB)
    (agreeM : ∀ y, M y = if side y then B y else A y)
    (agreeN : ∀ y, N y = if side y then A y else B y)
    (fixedA : ∀ y, accept y = true → A y = y)
    (fixedB : ∀ y, accept y = true → B y = y) :
    (∀ T, accept (M^[T] z) = false) ∧ (∀ T, accept (N^[T] z) = false) := by sorry
