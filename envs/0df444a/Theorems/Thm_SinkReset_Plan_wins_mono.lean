-- Prove2me | Theorems.Thm_SinkReset_Plan_wins_mono
-- name    : SinkReset.Plan.wins_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:42:51.354583+00:00
-- url     : https://prove2.me/theorems/342bf387-0074-426e-8994-e60d2bd7581d
-- title:
--   Plan: wins mono
-- statement:
--   The Plan construction uses the wins mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L123-L128
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L123-L128

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.wins_mono {k : ℕ} {S T : Finset (Fin n)}
    (h : A.AliceWins k T) (hST : S ⊆ T) : A.AliceWins k S := by sorry
