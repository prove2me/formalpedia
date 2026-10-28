-- Prove2me | Theorems.Thm_RuntimeTransfer_fourier_arithmetic_transfer
-- name    : RuntimeTransfer.fourier_arithmetic_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:20:28.711386+00:00
-- url     : https://prove2.me/theorems/7405a122-c185-4746-bcd0-9387f87f4e33
-- title:
--   Fourier transfer with proved arithmetic overhead
-- statement:
--   For every natural $n$, nonzero complex $\rho$, length-$n$ input $x$, and correct full-product oracle whose charge on every query of lengths $n$ and $2n+1$ is at most $P(2n+1)$, the concrete program returns the array $\sum_j x_j(\rho^2)^{jk}$ and has charged cost at most $P(2n+1)+6n+7$. The local count is one inversion and $6n+6$ multiplications, with structural array/control operations uncharged. No monotonicity or scaling assumption on $P$ is required. When $\rho^2$ is the desired primitive root, the output is the unnormalised DFT. This is an arithmetic-operation result, not a bit/RAM bound.
-- source:
--   Strengthened transfer results, companion note to this mission, 24 October 2026. Concrete instruction-count and bit-length formulation of classical Bluestein and Kronecker reductions; not a claim of a new complexity exponent. Theorem 5, main transfer inequality.

import Definitions.Def_RuntimeTransferArithmetic
set_option autoImplicit false
open RuntimeTransfer

theorem RuntimeTransfer.fourier_arithmetic_transfer {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0)
    (x : Fin n → ℂ) (oracle : FourierQuery n → (Fin (3 * n + 1) → ℂ) × ℕ)
    (P : ℕ → ℕ) (hcorrect : ∀ q, (oracle q).1 = fullProduct q)
    (hcost : ∀ q, (oracle q).2 ≤ P (2 * n + 1)) :
    ((fourierArithmetic ρ x).run oracle).1 = fourierValue ρ x ∧
      ((fourierArithmetic ρ x).run oracle).2 ≤ P (2 * n + 1) + 6 * n + 7 := by sorry
