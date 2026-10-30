-- Prove2me | Theorems.Thm_StochasticProg_PartitionJensen_jensen_ereal
-- name    : StochasticProg.PartitionJensen.jensen_ereal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:43:51.273057+00:00
-- url     : https://prove2.me/theorems/9cd5eb51-a984-4dab-83d2-d39db052ff23
-- title:
--   Chapter 8, §8.2, Exercise 2 — Jensen's inequality $\mathrm E(g(\xi)) \ge g(\mathrm E(\xi))$, allowing $\mathrm E(g(\xi)) = +\infty$
-- statement:
--   Let $\xi$ be a random vector in $\mathbb R^N$ with law $\mu$ and finite mean $\mathrm E(\xi) = \int \xi\, \mu(d\xi)$, and let $g : \mathbb R^N \to \mathbb R$ be convex on a convex set $C$ that carries $\xi$, $\mu(C^{\mathrm c}) = 0$ (the values of $g$ outside $C$ are arbitrary). Then:
--
--   1. the negative part of $g(\xi)$ has finite expectation, $\mathrm E\big(g(\xi)^-\big) < \infty$, so $\mathrm E(g(\xi)) = \mathrm E\big(g(\xi)^+\big) - \mathrm E\big(g(\xi)^-\big)$ is a well-defined element of $(-\infty, +\infty]$;
--   2. Jensen's inequality holds:
--
--   $$
--   \mathrm E(g(\xi)) \;\ge\; g(\mathrm E(\xi)) .
--   $$
--
--   No integrability of $g(\xi)$ is assumed; when $\mathrm E(g(\xi)) = +\infty$ the inequality holds trivially. In §8.2 of Birge and Louveaux this inequality is applied on every cell of a partition of the support to obtain the Jensen lower bound (Theorem 1); the book states it as Exercise 2 of §8.2, and also in Section 4.3 (printed p. 166).
--
--   **Formalization Note** $\mathbb R^N$ is `EuclideanSpace ℝ (Fin N)`, $\xi$ is the identity map under its law $\mu$ (a probability measure), and $\mathrm E(g(\xi))$ is the extended real `∫⁻ g⁺ dμ − ∫⁻ g⁻ dμ` in `EReal`; conclusion 1 is what makes this subtraction the book's value.
--
--   Differences from the source:
--   - encoding: a random vector ξ with distribution P → a probability measure μ on EuclideanSpace ℝ (Fin N), ξ the identity; reason: both sides depend only on the law of ξ
--   - encoding: E(ξ) exists (presupposed by the statement) → hypothesis Integrable (fun ξ => ξ) μ; reason: the book's g(E(ξ)) presupposes a finite mean
--   - reading: g convex → g : ℝ^N → ℝ real-valued and convex on a convex set C with μ(Cᶜ) = 0 (values outside C unconstrained); reason: the book's convex functions may take the value +∞ (Section 2.11, printed p. 98, PDF p. 124); C = ℝ^N is a finite convex function on ℝ^N, C = dom g covers a proper convex integrand finite almost surely, and integrands such as 1/ξ or −log ξ of a positive ξ are included; an integrand equal to +∞ with positive probability has E = +∞, where the bound is immediate
--   - encoding: E(g(ξ)), possibly +∞ → EReal value ∫⁻ g⁺ − ∫⁻ g⁻ together with the conclusion ∫⁻ g⁻ ≠ ∞; reason: this is the book's expectation in (−∞, +∞]; the clause rules out the undefined ∞ − ∞
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 8, §8.2, Exercise 2, printed p. 352 (PDF p. 371): "Prove Jensen's inequality, E(g(ξ)) ≥ g(E(ξ)), by taking an expectation of the points on a supporting hyperplane to g(ξ) at g(E(ξ))." Also Section 4.3, printed p. 166 (PDF p. 190).

import Mathlib
open MeasureTheory

namespace StochasticProg.PartitionJensen

/-- **Jensen's inequality, `E(g(ξ)) ≥ g(E(ξ))` — §8.2 Exercise 2.**
Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, Chapter 8,
§8.2, Exercise 2, printed p. 352 (PDF p. 371): "Prove Jensen's inequality, E(g(ξ)) ≥ g(E(ξ)),
by taking an expectation of the points on a supporting hyperplane to g(ξ) at g(E(ξ))."
(The book also states it in Section 4.3, printed p. 166, PDF p. 190.)

Let `μ` be the law of a random vector `ξ` in `ℝ^N` with a finite mean `E(ξ) = ∫ ξ dμ`, and let
`g` be convex on a convex set `C` that carries `ξ` (`μ Cᶜ = 0`). Then the negative part of `g(ξ)` has finite expectation, so
`E(g(ξ)) ∈ (-∞, +∞]` is well defined, and `E(g(ξ)) ≥ g(E(ξ))`.

**Formalization Note.** `ℝ^N` is `EuclideanSpace ℝ (Fin N)` and `ξ` is the identity map under
its law `μ`. `E(g(ξ))` is the extended real `∫⁻ g⁺ dμ − ∫⁻ g⁻ dμ` (positive minus negative
part); the first conclusion `∫⁻ g⁻ dμ ≠ ∞` makes this subtraction the book's value (never
`∞ − ∞`). No integrability or measurability of `g(ξ)` is assumed, so `E(g(ξ)) = +∞` is covered.
"Convex" is read as real-valued and convex on a convex set `C` of full measure (values outside
`C` are unconstrained); `C = univ` is a finite convex function on `ℝ^N`. -/
theorem jensen_ereal {N : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [IsProbabilityMeasure μ]
    (hξ : Integrable (fun ξ => ξ) μ)
    (C : Set (EuclideanSpace ℝ (Fin N))) (hCμ : μ Cᶜ = 0)
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (hg : ConvexOn ℝ C g) :
    (∫⁻ ξ, ENNReal.ofReal (-g ξ) ∂μ) ≠ ⊤ ∧
      ((g (∫ ξ, ξ ∂μ) : ℝ) : EReal) ≤
        ((∫⁻ ξ, ENNReal.ofReal (g ξ) ∂μ : ENNReal) : EReal) -
          ((∫⁻ ξ, ENNReal.ofReal (-g ξ) ∂μ : ENNReal) : EReal) := by sorry

end StochasticProg.PartitionJensen
