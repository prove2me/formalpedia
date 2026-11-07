-- Prove2me | Theorems.Thm_SoftmaxAttnFD_lemma_2_6
-- name    : SoftmaxAttnFD.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:01:35.06998+00:00
-- url     : https://prove2.me/theorems/cb3c8aca-6e4a-4968-9f24-b2d83e8432c2
-- title:
--   Lemma 2.6, p.12 — temperature interpolation
-- statement:
--   Let $n_{\rm int}\ge2$ be an integer, $\beta_{\rm lo}>0$, and let
--   $$\tau_\ell=\beta_{\rm lo}\Bigl(\frac54+\frac{\ell}{2(n_{\rm int}-1)}\Bigr)\quad(0\le\ell<n_{\rm int}),\qquad L_\ell(\beta)=\prod_{\ell'\ne\ell}\frac{\beta-\tau_{\ell'}}{\tau_\ell-\tau_{\ell'}}.$$
--   The $n_{\rm int}$ nodes define a Lagrange interpolation polynomial of degree at most $n_{\rm int}-1$. For all $\mu\ge0$ and $\beta\in[\beta_{\rm lo},2\beta_{\rm lo}]$,
--   $$\Bigl|e^{-\beta\mu}-\sum_\ell L_\ell(\beta)e^{-\tau_\ell\mu}\Bigr|\le\Bigl(\frac34\Bigr)^{n_{\rm int}}\quad\text{and}\quad\sum_\ell|L_\ell(\beta)|\le9^{n_{\rm int}-1}.$$
--   One set of nodes serves all rows of a group, whatever their temperatures, which is how Proposition 5.5 turns rows of different norms into a bounded number of biased products.
--
--   Differences from the source:
--   - encoding: "The n_int nodes define a Lagrange interpolation polynomial of degree at most n_int − 1" → for all data y, ∑ L_ℓ(β) y_ℓ is a polynomial of degree below n_int taking the value y_ℓ at τ_ℓ; reason: this is what that sentence asserts about the nodes
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Lemma 2.6, p.12

import Mathlib

namespace SoftmaxAttnFD

/-- **Lemma 2.6** (arXiv:2611.06055, sha256 a60f7609…, p.12). Temperature interpolation with the nodes
`τ_ℓ = β_lo(5/4 + ℓ/(2(n_int − 1)))`.

**Formalization Note** The first clause renders "The n_int nodes define a Lagrange interpolation
polynomial of degree at most n_int − 1": for all data `y`, the sum `∑_ℓ L_ℓ(β) y_ℓ` is a polynomial of
degree below `n_int` with value `y_ℓ` at `τ_ℓ`. -/
theorem lemma_2_6 (nint : ℕ) (hn : 2 ≤ nint) (βlo : ℝ) (hβ : 0 < βlo) (τ : Fin nint → ℝ)
    (hτ : ∀ ℓ, τ ℓ = βlo * (5 / 4 + (ℓ.val : ℝ) / (2 * ((nint : ℝ) - 1))))
    (L : Fin nint → ℝ → ℝ)
    (hL : ∀ ℓ β, L ℓ β = ∏ ℓ' ∈ Finset.univ.erase ℓ, (β - τ ℓ') / (τ ℓ - τ ℓ')) :
    (∀ y : Fin nint → ℝ, ∃ R : Polynomial ℝ, R.degree < (nint : ℕ) ∧
      (∀ β, R.eval β = ∑ ℓ, L ℓ β * y ℓ) ∧ ∀ ℓ, R.eval (τ ℓ) = y ℓ) ∧
    (∀ μ β : ℝ, 0 ≤ μ → βlo ≤ β → β ≤ 2 * βlo →
      |Real.exp (-β * μ) - ∑ ℓ, L ℓ β * Real.exp (-τ ℓ * μ)| ≤ (3 / 4 : ℝ) ^ nint ∧
      ∑ ℓ, |L ℓ β| ≤ (9 : ℝ) ^ (nint - 1)) := by sorry

end SoftmaxAttnFD
