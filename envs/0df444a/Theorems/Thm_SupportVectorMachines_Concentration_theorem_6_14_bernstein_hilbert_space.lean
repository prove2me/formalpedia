-- Prove2me | Theorems.Thm_SupportVectorMachines_Concentration_theorem_6_14_bernstein_hilbert_space
-- name    : SupportVectorMachines.Concentration.theorem_6_14_bernstein_hilbert_space
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:08:06.655288+00:00
-- url     : https://prove2.me/theorems/8bae422f-9394-4d0b-8bf0-453cc1025263
-- title:
--   Bernstein's inequality for independent Hilbert-space-valued random variables
-- statement:
--   This is Theorem 6.14 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008,
--   p. 216), a clean, self-contained generalization of the classical scalar Bernstein inequality
--   (Theorem 6.12) to Hilbert-space-valued random variables.
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space, $H$ a separable Hilbert space, $B,\sigma>0$,
--   and let $\xi_1,\dots,\xi_n : \Omega \to H$ be independent random variables with
--   $\mathbb E\,\xi_i = 0$, $\|\xi_i\|_\infty \le B$, and $\mathbb E\,\|\xi_i\|_H^2 \le \sigma^2$
--   for every $i$. Then, for every $\tau > 0$,
--
--   $$
--   P\!\left(\Big\|\frac1n\sum_{i=1}^n \xi_i\Big\|_H \ge
--     \sqrt{\frac{2\sigma^2\tau}{n}} + \sqrt{\frac{\sigma^2}{n}} + \frac{2B\tau}{3n}\right) \le e^{-\tau}.
--   $$
--
--   The tail bound has **three** terms, unlike the scalar Theorem 6.12's two: the middle term
--   $\sqrt{\sigma^2/n}$ is the dimension-independent price of concentrating a vector-valued
--   average, absent from the real-valued case. This inequality is used throughout the rest of the
--   book (directly, and via its Hilbert-space-Hoeffding corollary, Corollary 6.15) to control the
--   deviation of an empirical mean of Hilbert-space-valued quantities — such as the values
--   $\Phi(x_i)y_i$ occurring in the analysis of SVMs — around its expectation, which is exactly
--   the kind of vector-valued concentration a scalar inequality applied only to $\|\xi_i\|$ could
--   not deliver.
--
--   **Formalization Note** The norm in the conclusion, $\|\cdot\|_H$, is the Hilbert space norm
--   of the *average of the random variables themselves*, not a scalar reduction via
--   $\|\xi_i\|_H$: the goal genuinely concentrates a vector-valued quantity. $\|\xi_i\|_\infty\le B$
--   is the almost-sure bound `∀ᵐ ω ∂P, ‖ξ i ω‖ ≤ B`. $H$'s separability
--   (`TopologicalSpace.SeparableSpace H`) is a real hypothesis reused from Theorem 6.13's proof,
--   not boilerplate. Independence is of the $H$-valued random variables themselves (`iIndepFun`),
--   matching the book's use of mutual independence of the whole family in Theorem 6.13's proof,
--   which this theorem's own proof invokes.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 216, Theorem 6.14

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupportVectorMachines.Concentration

/-- Theorem 6.14 (Bernstein's inequality in Hilbert spaces), p. 216: let `(Ω, A, P)` be a
probability space, `H` be a separable Hilbert space, `B > 0`, and `σ > 0`. Let
`ξ₁,…,ξₙ : Ω → H` be independent random variables satisfying `E ξᵢ = 0`, `‖ξᵢ‖_∞ ≤ B`, and
`E ‖ξᵢ‖²_H ≤ σ²` for all `i = 1,…,n`. Then, for all `τ > 0`,
`P(‖(1/n) ∑ᵢ ξᵢ‖_H ≥ √(2σ²τ/n) + √(σ²/n) + 2Bτ/(3n)) ≤ e^{-τ}`. -/
theorem theorem_6_14_bernstein_hilbert_space {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
    (B σ : ℝ) (hB : 0 < B) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n) (ξ : Fin n → Ω → H)
    (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0) (hbound : ∀ i, ∀ᵐ ω ∂P, ‖ξ i ω‖ ≤ B)
    (hvar : ∀ i, ∫ ω, ‖ξ i ω‖ ^ 2 ∂P ≤ σ ^ 2) (τ : ℝ) (hτ : 0 < τ) :
    P.real {ω | Real.sqrt (2 * σ ^ 2 * τ / n) + Real.sqrt (σ ^ 2 / n) + 2 * B * τ / (3 * n) ≤
        ‖(1 / (n : ℝ)) • ∑ i, ξ i ω‖} ≤ Real.exp (-τ) := by sorry

end SupportVectorMachines.Concentration
