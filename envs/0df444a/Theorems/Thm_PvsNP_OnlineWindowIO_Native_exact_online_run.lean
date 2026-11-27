-- Prove2me | Theorems.Thm_PvsNP_OnlineWindowIO_Native_exact_online_run
-- name    : PvsNP.OnlineWindowIO.Native.exact_online_run
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T04:19:27.118844+00:00
-- url     : https://prove2.me/theorems/3d5db94d-55b1-4520-ab9a-eb64b8e121cd
-- title:
--   An online work-tape run has an exact native single-tape simulation
-- statement:
--   Given injective state and work symbol encodings with the blank encoded as none, the compiled native descriptor has one work tape and never moves its input head to the left. A terminating online run from blank tape of n successful transitions is simulated in n+1 transitions, emitting its prescribed verdict in the final transition.
-- source:
--   Exact simulation into the universal descriptor used by the P vs NP formalization.

import Definitions.Def_NativeOnlineSingleTape

set_option autoImplicit false
set_option maxHeartbeats 2000000

open PvsNP.OnlineWindowIO PvsNP.OnlineWindowIO.Native

theorem PvsNP.OnlineWindowIO.Native.exact_online_run
    {S A : Type} [Fintype S] [Fintype A] {M : OnlineMachine S A}
    (state : S ↪ ℕ) (symbol : A ↪ Option ℕ) (initial : S) (blank : A)
    (blankEncoded : symbol blank = none) (verdict : S → Option ℕ)
    {word : List Bool} {b : OnlineConfig S A} {n : ℕ}
    (run : OnlineRun M (⟨initial,0,fun _ => blank⟩,word) b n)
    (terminal : onlineStep M b = none) :
    (desc M state symbol initial verdict).tapes = 1 ∧
    (∀ row ∈ (desc M state symbol initial verdict).table, row.2.inputTape ≠ .neg) ∧
    Turing.MultiTapeTM.Universal.simulate (desc M state symbol initial verdict) (word.map Bool.toNat) (n+1) =
      ((verdict b.1.state).toList,true) := by sorry
