-- Prove2me | Theorems.Thm_RuntimeTransfer_fourier_arithmetic_exact
-- name    : RuntimeTransfer.fourier_arithmetic_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:20:28.879507+00:00
-- url     : https://prove2.me/theorems/2a95908c-2660-4570-9ebd-b682085197ba
-- title:
--   Exact Fourier reduction cost: $6n+7$ plus one product
-- statement:
--   For all natural $n$, nonzero complex $\rho$, input $x$, and a correct full-product oracle $O$, the concrete arithmetic program returns $\sum_j x_j(\rho^2)^{jk}$ in coordinate $k$, with cost exactly $6n+7+c(q)$, where $q$ is the chirp query and $c(q)$ is its actual oracle charge. Each explicit multiplication and inversion costs one; array/control work is uncharged. The formula includes $n=0$. Roots are supplied; no root-of-unity assumption is needed for the identity.
-- source:
--   Strengthened transfer results, companion note to this mission, 24 October 2026. Concrete instruction-count and bit-length formulation of classical Bluestein and Kronecker reductions; not a claim of a new complexity exponent. Theorem 5, exact interpreter equality.

import Definitions.Def_RuntimeTransferArithmetic
set_option autoImplicit false
open RuntimeTransfer

theorem RuntimeTransfer.fourier_arithmetic_exact {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0)
    (x : Fin n → ℂ) (oracle : FourierQuery n → (Fin (3 * n + 1) → ℂ) × ℕ)
    (hcorrect : ∀ q, (oracle q).1 = fullProduct q) :
    (fourierArithmetic ρ x).run oracle =
      (fourierValue ρ x, 6 * n + 7 + (oracle (chirpQuery ρ x)).2) := by sorry
