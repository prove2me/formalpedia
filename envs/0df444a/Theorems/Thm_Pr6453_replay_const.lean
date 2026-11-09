-- Prove2me | Theorems.Thm_Pr6453_replay_const
-- name    : Pr6453.replay_const
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T21:40:31.672015+00:00
-- url     : https://prove2.me/theorems/4864a242-e199-4639-a6d7-089739098dd5
-- title:
--   PR #6453: a program that avoids a column leaves its frame alone
-- statement:
--   A program that never writes the frame of a column leaves that column's frame where it was.
--
--   The frame of a column is written only by the events naming it — a move, an initialisation or a clear — while scaling and addition write no frame at all. So if every event of a program avoids column $c$, replaying the program returns the frame of $c$ unchanged.
--
--   This is the per-stage locality the replay proof of the 17 926-event word is organised around: a construction stage acts on a known set of columns, leaves every other column alone, and the stages are combined by composition of their replays.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: the guarded replay of research/p104-clean-piggyback/construct.py.

import Definitions.Def_Pr6453_Frames
import Definitions.Def_Pr6453_Locality

set_option autoImplicit false

namespace Pr6453

theorem replay_const {n : ℕ} (p : List (Event n)) (fr : Fin n → Option ℕ) (c : Fin n)
    (hw : ∀ e ∈ p, ¬ Writes e c) (g : Fin n → Option ℕ) (h : replayF? p fr = some g) :
    g c = fr c := by
  sorry

end Pr6453
