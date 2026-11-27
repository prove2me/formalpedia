-- Prove2me | Theorems.Thm_PvsNP_NativeStockTape_replay_step_exact
-- name    : PvsNP.NativeStockTape.replay_step_exact
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T02:42:28.646804+00:00
-- url     : https://prove2.me/theorems/10977213-51b9-48ce-902d-4a7baa2c0be6
-- title:
--   One native work tape exactly replays atomic stock tape transitions
-- statement:
--   For a finite state and alphabet stock atomic tape machine, the encoded native table simulates each transition on a single work tape with its physical input head parked at the right end. A stock halt halts the native machine and emits the designated answer. Each running step preserves the tape encoding invariant.
-- source:
--   Exact transition correspondence between Mathlib TM0 and the Complexitylib universal multitape model.

import Definitions.Def_StockOneWorkReplay

set_option autoImplicit false

open Turing.MultiTapeTM.Universal PvsNP.NativeStockTape

variable {Γ Λ : Type} [Inhabited Λ] [Inhabited Γ]

theorem PvsNP.NativeStockTape.replay_step_exact [Fintype Γ] [Fintype Λ] (M : Turing.TM0.Machine Γ Λ)
    (encodeState : Λ ↪ ℕ) (encodeSymbol : Γ → Option ℕ) (decode : Option ℕ → Γ)
    (inverse : Function.LeftInverse decode encodeSymbol) (blank : encodeSymbol default = none)
    (answer : Γ → Option ℕ) (setup : List (Key × Act)) (early : ∀ row ∈ setup, row.1.state < 3)
    (input : List ℕ) (q : Λ) (t : WorkTape) (valid : EncodedTape encodeSymbol t) :
    let native := step (replayDescriptor M encodeState encodeSymbol answer setup) input
      (packConfig input encodeState q t)
    match Turing.TM0.step M ⟨q,view decode t⟩ with
    | none => native.1.state = none ∧ native.2 = answer (view decode t).head
    | some next => ∃ u : WorkTape, native = (packConfig input encodeState next.q u,none) ∧
        EncodedTape encodeSymbol u ∧ view decode u = next.Tape := by sorry
