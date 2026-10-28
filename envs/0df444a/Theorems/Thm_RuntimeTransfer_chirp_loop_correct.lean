-- Prove2me | Theorems.Thm_RuntimeTransfer_chirp_loop_correct
-- name    : RuntimeTransfer.chirp_loop_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:20:30.014461+00:00
-- url     : https://prove2.me/theorems/1416d570-0b46-442c-9c03-515309ba8a5c
-- title:
--   Chirp generation in exactly $2m$ scalar instructions
-- statement:
--   For any natural $n,m$, nonzero complex $\rho$, integer offset $j$, and arbitrary product oracle, the chirp loop with stride $\rho^2$, initial value $\rho^{j^2}$, and initial multiplier $\rho^{2j+1}$ returns the length-$m$ array with entries $\rho^{(j+i)^2}$ and charged cost exactly $2m$. It makes no product-oracle calls. Structural array/control work and evaluation of the supplied initial operands are uncharged.
-- source:
--   Strengthened transfer results, companion note to this mission, 24 October 2026. Concrete instruction-count and bit-length formulation of classical Bluestein and Kronecker reductions; not a claim of a new complexity exponent. Theorem 5, chirp-generation invariant.

import Definitions.Def_RuntimeTransferArithmetic
set_option autoImplicit false
open RuntimeTransfer

theorem RuntimeTransfer.chirp_loop_correct {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0) (j : ℤ) (m : ℕ)
    (oracle : FourierQuery n → (Fin (3 * n + 1) → ℂ) × ℕ) :
    (chirpLoop (ρ ^ 2) (ρ ^ (j ^ 2)) (ρ ^ (2 * j + 1)) m).run oracle =
      ((fun i : Fin m => ρ ^ ((j + (i.val : ℤ)) ^ 2)), 2 * m) := by sorry
