-- Prove2me | Theorems.Thm_Real_exists_unique_zero_of_le_deriv_of_abs_lt
-- name    : Real.exists_unique_zero_of_le_deriv_of_abs_lt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:35:49.922954+00:00
-- url     : https://prove2.me/theorems/f32dcf50-ad80-4506-b563-8405dc3ee137
-- title:
--   A unique zero in a window where the derivative is bounded below
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be differentiable, $\eta>0$ and $c>0$, with $f'(\sigma)\ge c$ for $|\sigma|\le\eta$ and $|f(0)|<c\eta$. Then there is a unique $\sigma$ with $|\sigma|<\eta$ and $f(\sigma)=0$.
--
--   This is the one-dimensional quantitative inverse-function step: a root near $0$ with an explicit radius.
--
--   Formalization Note: existence and uniqueness are stated as `∃ σ, |σ| < η ∧ f σ = 0 ∧ ∀ σ', |σ'| < η → f σ' = 0 → σ' = σ`.
-- source:
--   Standard

import Mathlib

namespace Real

/-- Let `f : ℝ → ℝ` be differentiable, `η > 0`, `c > 0`, with `c ≤ f' σ` for `|σ| ≤ η` and
`|f 0| < c η`. Then `f` has exactly one zero `σ` with `|σ| < η`. -/
theorem exists_unique_zero_of_le_deriv_of_abs_lt {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {η c : ℝ} (hη : 0 < η) (hc : 0 < c)
    (hd : ∀ σ, |σ| ≤ η → c ≤ deriv f σ) (h0 : |f 0| < c * η) :
    ∃ σ, |σ| < η ∧ f σ = 0 ∧ ∀ σ', |σ'| < η → f σ' = 0 → σ' = σ := by
  sorry

end Real
