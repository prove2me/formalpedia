-- Prove2me | Theorems.Thm_Polynomial_haviland_real
-- name    : Polynomial.haviland_real
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T22:12:53.167303+00:00
-- url     : https://prove2.me/theorems/13aba22a-7790-41ec-9c7d-ce6b26e4c0ae
-- title:
--   Haviland representation for positive polynomial functionals on a closed subset of the real line
-- statement:
--   Let $K$ be any closed subset of the real line, and let $L:\mathbb R[x]\to\mathbb R$ be a real linear functional. Suppose that $L(p)\ge0$ whenever $p$ is nonnegative on $K$. Then there is a positive Borel measure $\mu$ concentrated on $K$ such that every real polynomial is $\mu$-integrable and
--
--   $$
--   L(p)=\int_{\mathbb R}p(x)\,d\mu(x)\qquad(p\in\mathbb R[x]),\qquad
--   \mu(\mathbb R\setminus K)=0.
--   $$
--
--   This is the one-dimensional closed-set form of Haviland's theorem. It supplies the measure-representation step for full Hamburger, Stieltjes and interval moment problems after positivity on the appropriate nonnegative polynomials has been established.
--
--   **Formalization Note** No probability normalization, strict positivity or nonempty-support assumption is imposed. Integrability of the constant polynomial implies that the representing measure is finite.
-- source:
--   Konrad Schmüdgen, Ten Lectures on the Moment Problem (2020), arXiv:2008.12698v1, Theorem 1.9, printed p.13 (PDF p.13), implication (i) to (ii), specialized to dimension one. https://arxiv.org/pdf/2008.12698v1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Polynomial.Module.Basic

open MeasureTheory
set_option autoImplicit false

theorem Polynomial.haviland_real (K : Set ℝ) (hK : IsClosed K)
    (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ p : Polynomial ℝ, (∀ x ∈ K, 0 ≤ p.eval x) → 0 ≤ L p) :
    ∃ μ : Measure ℝ, μ Kᶜ = 0 ∧
      ∀ p : Polynomial ℝ, Integrable (fun x : ℝ => p.eval x) μ ∧
        ∫ x, p.eval x ∂μ = L p := by sorry
