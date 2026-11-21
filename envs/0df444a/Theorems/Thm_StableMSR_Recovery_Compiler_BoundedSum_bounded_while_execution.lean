-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_while_execution
-- name    : StableMSR.Recovery.Compiler.BoundedSum.bounded_while_execution
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T18:00:59.377375+00:00
-- url     : https://prove2.me/theorems/6acb7e95-343a-4324-8387-0bab83e7c31b
-- title:
--   Charged execution of an indexed bounded loop
-- statement:
--   An indexed invariant with a uniform charged body bound yields a finite execution through index N. The result charges the two control instructions per iteration and the two exit instructions.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix B, Theorem B.2. Charged deterministic RAM implementation.

import Definitions.Def_StableMSR_BoundedSumRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial

theorem StableMSR.Recovery.Compiler.BoundedSum.bounded_while_execution {n : ℕ} (d : Point n→Point n→ℝ) (c : Cmd) (guard : Cond) (A : ℕ→Store→Prop)
    (N B : ℕ) (h : LoopBound d c guard A N B) (i : ℕ) (hi : i≤N) (s : Store) (hs : A i s) :
    ∃t z, Executes d (.whileDo guard c) s t z ∧ z≤(N-i)*(B+2)+2 ∧ A N t := by
  sorry
