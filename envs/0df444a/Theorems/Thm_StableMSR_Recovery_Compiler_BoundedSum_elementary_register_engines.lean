-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_elementary_register_engines
-- name    : StableMSR.Recovery.Compiler.BoundedSum.elementary_register_engines
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T18:01:09.240682+00:00
-- url     : https://prove2.me/theorems/5bbe57e6-186a-4287-8629-0230fe4f58b2
-- title:
--   Compilation of elementary natural arithmetic into pointer instructions
-- statement:
--   Constants and input projections each take one instruction. Two compiled operands in consecutive scratch registers implement addition, truncated subtraction and a comparison flag. All lower pointers and integer memory are preserved.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix B, Theorem B.2. Charged deterministic RAM implementation.

import Definitions.Def_StableMSR_BoundedSumRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial

theorem StableMSR.Recovery.Compiler.BoundedSum.elementary_register_engines : (∀a : ℕ, Engine (fun _=>a)) ∧ (∀i : ℕ,Engine (fun ρ=>ρ i)) ∧
    ∀ (o : Gate) (f g : Env→ℕ), Engine f → Engine g → Engine (fun ρ=>o.val (f ρ) (g ρ)) := by
  sorry
