-- Prove2me | Theorems.Thm_ReplayVerification_no_mismatch_after_deterministic_restart
-- name    : ReplayVerification.no_mismatch_after_deterministic_restart
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T20:04:23.876917+00:00
-- url     : https://prove2.me/theorems/10c33f5d-77d7-4e90-9b5d-e9f02c57e951
-- title:
--   Safety of a deterministic worker replayed to its first halt
-- statement:
--   A controller initializes a deterministic worker for the current input and runs it until the first state where its halting test is true. It records that state's reported value, resets the worker to the same initialized state, and replays it until its first halt. A mismatch enters a distinguished failure state. A match starts the same process on a specified successor input. For any worker, any initial input, any input successor function, and any finite number of controller steps, the failure state is unreachable. Worker running times may vary and a worker may never halt.
-- source:
--   Direct first-halt uniqueness and inductive safety proof for a deterministic replay controller.

import Mathlib

theorem ReplayVerification.no_mismatch_after_deterministic_restart {Input Work Result : Type*} [DecidableEq Result]
    (init : Input → Work) (next : Work → Work) (halt : Work → Bool)
    (report : Work → Result) (successor : Input → Input)
    (first : Input) (T : ℕ) :
    let Control := (Input × Work) ⊕ ((Input × Result × Work) ⊕ Unit)
    let step : Control → Control := fun
      | .inl (i, w) =>
        if halt w then .inr (.inl (i, report w, init i)) else .inl (i, next w)
      | .inr (.inl (i, claim, w)) =>
        if halt w then
          if report w = claim then .inl (successor i, init (successor i)) else .inr (.inr ())
        else .inr (.inl (i, claim, next w))
      | .inr (.inr ()) => .inr (.inr ())
    step^[T] (.inl (first, init first)) ≠ .inr (.inr ()) := by sorry
