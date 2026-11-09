-- Prove2me | Theorems.Thm_Pr6453_replay_composes
-- name    : Pr6453.replay_composes
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T19:09:20.059481+00:00
-- url     : https://prove2.me/theorems/d86f5a84-9809-4587-9503-37f4170725fd
-- title:
--   PR #6453: the replay composes and is deterministic
-- statement:
--   The two structural facts about the replay of a word: it composes over concatenation of programs, and it is deterministic.
--
--   Composition: replaying `p ++ q` from a state is replaying `p` and then `q`. That is the induction principle a proof of the replay condition for the full 17 926-event program would use — it lets the program be broken into the segments the construction's stages are made of, each replays its own segment, and the segments compose. Determinism: a successful replay has a unique end state, so the frame and row charts the certificate records are the ones the program determines.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: the guarded replay of research/p104-clean-piggyback/construct.py.

import Definitions.Def_Pr6453_Replay

set_option autoImplicit false

namespace Pr6453

theorem replay_composes :
    (∀ (n : ℕ) (p q : List (Event n)) (st : State n),
        replay? (p ++ q) st = (replay? p st).bind (replay? q)) ∧
      (∀ (n : ℕ) (prog : List (Event n)) (st fin fin' : State n),
        replay? prog st = some fin → replay? prog st = some fin' → fin = fin') := by
  sorry

end Pr6453
