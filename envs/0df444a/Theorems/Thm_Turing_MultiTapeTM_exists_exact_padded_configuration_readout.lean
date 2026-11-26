-- Prove2me | Theorems.Thm_Turing_MultiTapeTM_exists_exact_padded_configuration_readout
-- name    : Turing.MultiTapeTM.exists_exact_padded_configuration_readout
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T19:48:06.039907+00:00
-- url     : https://prove2.me/theorems/e98fd8c3-f2c5-5c0b-af8c-842fd93881a8
-- title:
--   Exact configuration addresses for a time-padded multitape machine
-- statement:
--   Let a deterministic multitape Turing machine have finitely many control states. Add one work tape and keep the alphabet, assuming a marker symbol is available. The new machine starts with blank work tapes. For a nonempty input of length $n$, write the worker time as $t=qn+r$ with $0$ at most $r$ and $r<n$. At the physical time $2n+2+q(2n+2)+r$, a fixed projection of the new machine's configuration is exactly the original configuration at time $t$, including its halting flag, heads, tapes, and output. The physical time is at most $2n+2+4t$.
-- source:
--   Direct clock construction in the deterministic Cslib multitape Turing machine model. The statement includes blank-tape initialization and exact addresses for all worker indices.

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic

universe u v

open Turing Turing.MultiTapeTM

theorem Turing.MultiTapeTM.exists_exact_padded_configuration_readout {k : ℕ} {S : Type u} {Q : Type v} [Finite Q]
    (worker : MultiTapeTM k S Q) (mark : S) :
    ∃ (R : Type v) (_finite : Finite R) (wrapper : MultiTapeTM (k+1) S R)
      (projectState : ∀ {input : List S}, Cfg (k+1) S R input → Cfg k S Q input),
      ∀ (input : List S), 0 < input.length → ∀ t : ℕ,
        let n := input.length
        let address := (2*n+2) + (t/n)*(2*n+2) + t%n
        projectState (wrapper.runFrom (wrapper.initCfg input) address) =
          worker.runFrom (worker.initCfg input) t ∧
        address ≤ 2*n+2+4*t := by sorry
