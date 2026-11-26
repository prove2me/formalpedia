-- Prove2me | Theorems.Thm_UntimedCrossings_exchange_endpoints
-- name    : UntimedCrossings.exchange_endpoints
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T21:56:21.956566+00:00
-- url     : https://prove2.me/theorems/f699ed0e-a5c9-5f1d-b629-919ece98cd31
-- title:
--   Equal untimed crossing records preserve paired endpoints and total time
-- statement:
--   Two deterministic transition maps start at one state and run for possibly different finite durations. Their crossing records, which list destination states and omit timestamps, are equal. Form the two complementary mixed maps by using one original transition map on each side. There exist two finite durations, one per mixed map, whose sum equals the sum of the original durations. At these durations the mixed endpoints are the two original endpoints, in either order.
-- source:
--   A paired crossing-sequence argument inspired by F. C. Hennie, One-tape, off-line Turing machine computations, 1965.

import Definitions.Def_UntimedEndpointExchange

open UntimedCrossings

theorem UntimedCrossings.exchange_endpoints {S : Type*} (side : S → Bool)
    (A B M N : S → S) (z : S) (stepsA stepsB : ℕ)
    (records : untimedRecord side A z stepsA = untimedRecord side B z stepsB)
    (agreeM : ∀ x, M x = if side x then B x else A x)
    (agreeN : ∀ x, N x = if side x then A x else B x) :
    ∃ m n : ℕ, m+n = stepsA+stepsB ∧
      ((M^[m] z = A^[stepsA] z ∧ N^[n] z = B^[stepsB] z) ∨
       (M^[m] z = B^[stepsB] z ∧ N^[n] z = A^[stepsA] z)) := by sorry
