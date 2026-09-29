-- Prove2me | Theorems.Thm_SupportVectorMachines_Concentration_theorem_6_12_bernstein_scalar
-- name    : SupportVectorMachines.Concentration.theorem_6_12_bernstein_scalar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:07:18.58098+00:00
-- url     : https://prove2.me/theorems/44ebabe6-dc88-42d5-951d-513aabd159ad
-- title:
--   Bernstein's inequality (scalar case)
-- statement:
--   This is Theorem 6.12 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008,
--   p. 213), the classical scalar Bernstein inequality that Theorem 6.14 generalizes to
--   Hilbert-space-valued random variables.
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space, $B,\sigma>0$, $n\ge1$ an integer, and let
--   $\xi_1,\dots,\xi_n : \Omega \to \mathbb R$ be independent random variables with
--   $\mathbb E\,\xi_i = 0$, $\|\xi_i\|_\infty \le B$ (an almost-sure bound), and
--   $\mathbb E\,\xi_i^2 \le \sigma^2$ for every $i$. Then, for every $\tau > 0$,
--
--   $$
--   P\!\left(\frac1n\sum_{i=1}^n \xi_i \ge \sqrt{\frac{2\sigma^2\tau}{n}} + \frac{2B\tau}{3n}\right) \le e^{-\tau}.
--   $$
--
--   This refines Hoeffding's inequality (Theorem 6.10) by using the variance bound $\sigma^2$ in
--   addition to the range bound $B$: when $\sigma^2$ is much smaller than $B^2$ (a low-variance
--   situation), Bernstein's bound is substantially sharper.
--
--   **Formalization Note** $\|\xi_i\|_\infty \le B$ is formalized as the almost-sure bound
--   `∀ᵐ ω ∂P, |ξ i ω| ≤ B`, matching the book's own $L^\infty(P)$ convention rather than a bound
--   holding for literally every $\omega$. Independence is the mutual independence of the whole
--   family (`iIndepFun`), matching the proof's use of $\mathbb E \exp(t\sum_i \xi_i) =
--   \prod_i \mathbb E \exp(t\xi_i)$.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 213, Theorem 6.12

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupportVectorMachines.Concentration

/-- Theorem 6.12 (Bernstein's inequality), p. 213: let `(Ω, A, P)` be a probability space,
`B > 0` and `σ > 0` be real numbers, and `n ≥ 1` be an integer. Let `ξ₁,…,ξₙ : Ω → ℝ` be
independent random variables satisfying `E ξᵢ = 0`, `‖ξᵢ‖_∞ ≤ B`, and `E ξᵢ² ≤ σ²` for all
`i = 1,…,n`. Then, for all `τ > 0`,
`P((1/n) ∑ᵢ ξᵢ ≥ √(2σ²τ/n) + 2Bτ/(3n)) ≤ e^{-τ}`. -/
theorem theorem_6_12_bernstein_scalar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B σ : ℝ) (hB : 0 < B) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (ξ : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0) (hbound : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ B)
    (hvar : ∀ i, ∫ ω, (ξ i ω) ^ 2 ∂P ≤ σ ^ 2) (τ : ℝ) (hτ : 0 < τ) :
    P.real {ω | Real.sqrt (2 * σ ^ 2 * τ / n) + 2 * B * τ / (3 * n) ≤
        (1 / (n : ℝ)) * ∑ i, ξ i ω} ≤ Real.exp (-τ) := by sorry

end SupportVectorMachines.Concentration
