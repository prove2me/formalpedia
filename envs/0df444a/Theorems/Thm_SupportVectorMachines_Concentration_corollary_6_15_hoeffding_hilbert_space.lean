-- Prove2me | Theorems.Thm_SupportVectorMachines_Concentration_corollary_6_15_hoeffding_hilbert_space
-- name    : SupportVectorMachines.Concentration.corollary_6_15_hoeffding_hilbert_space
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:08:26.594041+00:00
-- url     : https://prove2.me/theorems/514bcb02-0d0b-413b-b1dd-aa8bc2ebd19b
-- title:
--   Hoeffding's inequality for independent Hilbert-space-valued random variables
-- statement:
--   This is Corollary 6.15 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008,
--   p. 217), an immediate consequence of Theorem 6.14 by centering, used later in the book
--   (§6.4) to derive an oracle inequality for SVMs.
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space, $H$ a separable Hilbert space, and
--   $B > 0$. Let $\xi_1,\dots,\xi_n : \Omega \to H$ be independent $H$-valued random variables
--   with $\|\xi_i\|_\infty \le B$ for every $i$ (no mean-zero assumption is needed — the
--   statement centers each $\xi_i$ itself). Then, for every $\tau > 0$,
--
--   $$
--   P\!\left(\Big\|\frac1n\sum_{i=1}^n (\xi_i - \mathbb E\,\xi_i)\Big\|_H \ge
--     B\sqrt{\frac{2\tau}{n}} + B\sqrt{\frac1n} + \frac{4B\tau}{3n}\right) \le e^{-\tau}.
--   $$
--
--   Unlike Theorem 6.14, no variance bound $\sigma^2$ is assumed or needed: bounding $\eta_i :=
--   \xi_i - \mathbb E\,\xi_i$ by $2B$ (from the triangle inequality) and its variance by $B^2$
--   (from $\mathbb E\|\xi_i\|^2\ge \|\mathbb E\,\xi_i\|^2$) and applying Theorem 6.14 to the
--   $\eta_i$ recovers the stated bound directly.
--
--   **Formalization Note** The centering term $\mathbb E\,\xi_i$ is written as the Bochner
--   integral `∫ ω', ξ i ω' ∂P`; no separate mean-zero hypothesis is assumed, matching the book's
--   own statement, which centers the $\xi_i$ inside the claim rather than assuming they are
--   already centered.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 217, Corollary 6.15

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupportVectorMachines.Concentration

/-- Corollary 6.15 (Hoeffding's inequality in Hilbert spaces), p. 217: let `(Ω, A, P)` be a
probability space, `H` be a separable Hilbert space, and `B > 0`. Let `ξ₁,…,ξₙ : Ω → H` be
independent `H`-valued random variables satisfying `‖ξᵢ‖_∞ ≤ B` for all `i = 1,…,n`. Then, for
all `τ > 0`,
`P(‖(1/n) ∑ᵢ (ξᵢ - E ξᵢ)‖_H ≥ B√(2τ/n) + B√(1/n) + 4Bτ/(3n)) ≤ e^{-τ}`. -/
theorem corollary_6_15_hoeffding_hilbert_space {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
    (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 0 < n) (ξ : Fin n → Ω → H)
    (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hbound : ∀ i, ∀ᵐ ω ∂P, ‖ξ i ω‖ ≤ B) (τ : ℝ) (hτ : 0 < τ) :
    P.real {ω | B * Real.sqrt (2 * τ / n) + B * Real.sqrt (1 / n) + 4 * B * τ / (3 * n) ≤
        ‖(1 / (n : ℝ)) • ∑ i, (ξ i ω - ∫ ω', ξ i ω' ∂P)‖} ≤ Real.exp (-τ) := by sorry

end SupportVectorMachines.Concentration
