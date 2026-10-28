-- Prove2me | Theorems.Thm_RuntimeTransfer_fourier_same_order
-- name    : RuntimeTransfer.fourier_same_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:20:34.716664+00:00
-- url     : https://prove2.me/theorems/d8a154d0-3109-4d9f-a118-25f8e39110ac
-- title:
--   Same-order Fourier transfer under scaling bounds
-- statement:
--   For $n\ge1$, a nonzero complex $\rho$, input $x$, and correct full-product oracle costing at most $P(2n+1)$ per query, suppose $P(2n+1)\le C P(n)$ and $n\le P(n)$. Then the concrete Fourier program is correct and its charged arithmetic cost is at most $(C+13)P(n)$. The assumptions are pointwise at this $n$; no global monotonicity is assumed. Array/control operations are uncharged.
-- source:
--   Strengthened transfer results, companion note to this mission, 24 October 2026. Concrete instruction-count and bit-length formulation of classical Bluestein and Kronecker reductions; not a claim of a new complexity exponent. Theorem 6, pointwise scaling bound.

import Definitions.Def_RuntimeTransferArithmetic
set_option autoImplicit false
open RuntimeTransfer

theorem RuntimeTransfer.fourier_same_order {n : ℕ} (hn : 1 ≤ n) (ρ : ℂ) (hρ : ρ ≠ 0)
    (x : Fin n → ℂ) (oracle : FourierQuery n → (Fin (3 * n + 1) → ℂ) × ℕ)
    (P : ℕ → ℕ) (C : ℕ) (hcorrect : ∀ q, (oracle q).1 = fullProduct q)
    (hcost : ∀ q, (oracle q).2 ≤ P (2 * n + 1))
    (hscale : P (2 * n + 1) ≤ C * P n) (hlinear : n ≤ P n) :
    ((fourierArithmetic ρ x).run oracle).1 = fourierValue ρ x ∧
      ((fourierArithmetic ρ x).run oracle).2 ≤ (C + 13) * P n := by sorry
