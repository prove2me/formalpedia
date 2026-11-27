-- Prove2me | Theorems.Thm_PvsNP_OnlineMailbox_replay_halt
-- name    : PvsNP.OnlineMailbox.replay_halt
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T04:12:29.611691+00:00
-- url     : https://prove2.me/theorems/f76d8b34-5cae-4cb2-a518-422c22bf42a6
-- title:
--   A one-bit mailbox preserves a terminating online consumer run
-- statement:
--   If a generator emits a finite Boolean word in g transitions and a consumer halts on that word after i transitions, interleaving them through one cached symbol reaches the same consumer state and preserves its virtual unread suffix. The number of executed transitions plus pending generator work is i + g + 1.
-- source:
--   A correctness and clock bound for demand-driven composition of one-way stream machines.

import Definitions.Def_OnlineBooleanMailbox

set_option autoImplicit false

open PvsNP.OnlineMailbox

theorem PvsNP.OnlineMailbox.replay_halt {G C : Type} (p : Producer G) (c : Consumer C)
    {x : Source G} {out : List Bool} {g : ℕ} (producer : Produces p x out g)
    {r : C} {v : Virtual C} {i : ℕ} (run : Steps (consume c) i (r, out) v)
    (done : c v.1 v.2.head? = none) :
    ∃ (y : Source G) (used pending : ℕ),
      Steps (step p c) used (⟨x, r, .waiting⟩ : Combined G C)
        ⟨y, v.1, .ready v.2.head?⟩ ∧
      step p c ⟨y, v.1, .ready v.2.head?⟩ = none ∧
      Pending p (.ready v.2.head?) y v.2 pending ∧ used + pending = i + g + 1 := by sorry
