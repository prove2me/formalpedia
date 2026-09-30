-- Prove2me | Theorems.Thm_ShannoCG_SCONB_grad_eq_add_sum
-- name    : ShannoCG.SCONB.grad_eq_add_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T07:14:46.89413+00:00
-- url     : https://prove2.me/theorems/69a5009b-b8be-4a51-a006-c2de5fe3eb92
-- title:
--   Eq. (41): gradients along a run on a quadratic
-- statement:
--   Let $A$ be a real $n\times n$ matrix and $c \in \mathbb R^n$, and let the gradient be affine, $g(x) = Ax + c$ (for the quadratic $f(x) = \tfrac12 (x-\hat x)'A(x-\hat x) + b$ one has $c = -A\hat x$). Let $t < k$ and let iterates satisfy $x_{i+1} = x_i + p_i$ for $t < i \le k$, with $g_i = g(x_i)$. Then
--
--   $$g_{k+1} = A\left(x_{t+1} + \sum_{i=t+1}^{k} p_i\right) + c = g_{t+1} + \sum_{i=t+1}^{k} A p_i.$$
--
--   This expresses the current gradient through the gradient after the restart step and the later steps; it is used to show that the restart step stays orthogonal to later gradients.
--
--   **Formalization Note** Iterates and gradients are sequences indexed by $\mathbb N$, with $g_i = Ax_i + c$ for all $i$. The sum runs over `Finset.Ioc t k`. Positive definiteness of $A$ is not needed and not assumed.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 251 (PDF p. 8), §IV, eq. (41)

import Mathlib

open Matrix

namespace ShannoCG.SCONB

/-- Shanno, *Conjugate Gradient Methods with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §IV, p. 251 (PDF 8), eq. (41): on a quadratic with gradient `g(x) = Ax + c`, if
`x_{i+1} = x_i + p_i` for `t < i ≤ k`, then
`g_{k+1} = A(x_{t+1} + ∑_{i=t+1}^k p_i) + c = g_{t+1} + ∑_{i=t+1}^k A p_i`.

**Formalization Note.** Vectors are `Fin n → ℝ`, iterates `x, p : ℕ → Fin n → ℝ` and gradients
`g : ℕ → Fin n → ℝ` with `g i = A *ᵥ x i + c` (the gradient of (4) is the case `c = −A x̂`; the paper
writes `Ax + b` here). The sum `∑_{i=t+1}^k` is over `Finset.Ioc t k`. Positive definiteness of `A`
is not needed for this identity and is not assumed. `t < k` is kept as in the paper (the identity
also holds, with an empty sum, at `k = t`). -/
theorem grad_eq_add_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (x p g : ℕ → Fin n → ℝ) (t k : ℕ) (htk : t < k)
    (hg : ∀ i, g i = A *ᵥ x i + c)
    (hstep : ∀ i, t < i → i ≤ k → x (i + 1) = x i + p i) :
    g (k + 1) = A *ᵥ (x (t + 1) + ∑ i ∈ Finset.Ioc t k, p i) + c ∧
      g (k + 1) = g (t + 1) + ∑ i ∈ Finset.Ioc t k, A *ᵥ p i := by sorry

end ShannoCG.SCONB
