-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_natural_arithmetic
-- name    : StableMSR.Recovery.Compiler.BoundedSum.bounded_natural_arithmetic
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T18:01:13.759181+00:00
-- url     : https://prove2.me/theorems/78c05498-27b9-422a-9cbc-f2d15754652a
-- title:
--   Products, quotients and remainders are bounded-sum computations
-- statement:
--   Multiplication is bounded repeated addition. Division by a positive natural counts its positive multiples up to the dividend. The zero divisor and remainder follow the natural-number conventions.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix B, Theorem B.2. Charged deterministic RAM implementation.

import Definitions.Def_StableMSR_BoundedSumRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial

theorem StableMSR.Recovery.Compiler.BoundedSum.bounded_natural_arithmetic : (∀ f g : Env→ℕ,Form f → Form g → Form (fun ρ=>f ρ*g ρ)) ∧
    (∀ f g : Env→ℕ,Form f → Form g → Form (fun ρ=>f ρ/g ρ)) ∧
    (∀ f g : Env→ℕ,Form f → Form g → Form (fun ρ=>f ρ%g ρ)) := by
  sorry
