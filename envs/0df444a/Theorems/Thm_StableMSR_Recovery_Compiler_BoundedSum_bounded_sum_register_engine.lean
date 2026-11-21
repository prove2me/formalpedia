-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_sum_register_engine
-- name    : StableMSR.Recovery.Compiler.BoundedSum.bounded_sum_register_engine
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T18:01:23.567452+00:00
-- url     : https://prove2.me/theorems/f2ae9da7-bad9-4717-b001-4aab9550e259
-- title:
--   Uniform polynomial-time RAM compilation of a bounded sum
-- statement:
--   Evaluate the bound once and run a counted loop with a fresh index pointer. The body has access to that index and the original environment. Its polynomial time and value bounds compose with the bound polynomial.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix B, Theorem B.2. Charged deterministic RAM implementation.

import Definitions.Def_StableMSR_BoundedSumRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial

theorem StableMSR.Recovery.Compiler.BoundedSum.bounded_sum_register_engine (f g : Env→ℕ) (hf : Engine f) (hg : Engine g) :
    Engine (fun ρ=>∑ i ∈ Finset.range (f ρ),g (push i ρ)) := by
  sorry
