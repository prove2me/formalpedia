-- Prove2me | Theorems.Thm_RuntimeTransfer_fourier_oracle_transfer
-- name    : RuntimeTransfer.fourier_oracle_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:20:27.353531+00:00
-- url     : https://prove2.me/theorems/fdd69f51-8512-498f-b83b-5eef39741bb4
-- title:
--   One-query Fourier transfer with explicit overhead
-- statement:
--   For every natural $n$, nonzero complex $\rho$, input array $x$, and middle-product oracle correct on every query of the prescribed lengths with cost at most $T$, the chirp program returns $\sum_j x_j(\rho^2)^{jk}$ in coordinate $k$ and has accounted cost at most $E+D+T$. The nonnegative integers $E,D$ are explicit work charges. This does not prove their implementation cost; identifying the output as a DFT requires $\rho^2$ to be the desired root of unity.
-- source:
--   General runtime transfer and its Fourier/packing applications, companion proof note for this mission, 24 October 2026. Original cost-semantics formulation of standard substitution principles; not a claimed new complexity bound. Theorem 3, oracle-cost wrapper in the companion Lean formulation.

import Definitions.Def_RuntimeTransferFourier
set_option autoImplicit false
open RuntimeTransfer

theorem RuntimeTransfer.fourier_oracle_transfer {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0)
    (x : Fin n → ℂ) (oracle : FourierQuery n → (Fin n → ℂ) × ℕ)
    (T E D : ℕ) (hcorrect : ∀ q, (oracle q).1 = middleProduct q)
    (hcost : ∀ q, (oracle q).2 ≤ T) :
    ((fourierProgram ρ x E D).run oracle).1 = fourierValue ρ x ∧
      ((fourierProgram ρ x E D).run oracle).2 ≤ E + D + T := by sorry
