-- Prove2me | Theorems.Thm_StochasticProg_PartitionJensen_cell_jensen
-- name    : StochasticProg.PartitionJensen.cell_jensen
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:44:09.038412+00:00
-- url     : https://prove2.me/theorems/bb9660a5-6095-49a5-b644-34e80ea97b2b
-- title:
--   Chapter 8, eq. (2.2), last step — Jensen's inequality on one cell, $p^l\,\mathrm E[g(\xi) \mid S^l] \ge p^l g(\mathrm E[\xi \mid S^l])$
-- statement:
--   Let $\xi$ be a random vector in $\mathbb R^N$ with law $\mu$ and finite mean, let $S \subseteq \mathbb R^N$ be a measurable set with probability $p = \mathrm P[\xi \in S]$ and conditional mean $\xi_S = \mathrm E[\xi \mid S]$, and let $g : \mathbb R^N \to \mathbb R$ be convex on a convex set $C$ that carries $\xi$, $\mu(C^{\mathrm c}) = 0$ (the values of $g$ outside $C$ are arbitrary). Then:
--
--   1. the negative part of $g$ has finite integral over $S$, so $\int_S g(\xi)\,\mu(d\xi) = p\,\mathrm E[g(\xi) \mid S]$ is a well-defined element of $(-\infty, +\infty]$;
--   2. Jensen's inequality holds on the cell:
--
--   $$
--   \int_S g(\xi)\, \mu(d\xi) \;\ge\; p\, g(\xi_S) .
--   $$
--
--   In the proof of Theorem 1 of §8.2 of Birge and Louveaux, this is the termwise content of the last inequality of (2.2), $\sum_l p^l \mathrm E[g(x,\xi) \mid S^l] \ge \sum_l p^l g(x, \mathrm E[\xi \mid S^l])$, which "follows from Jensen's inequality".
--
--   **Formalization Note** $\mathbb R^N$ is `EuclideanSpace ℝ (Fin N)`, $p$ is `μ.real S` and $\xi_S$ is the set average `⨍ ξ in S, ξ ∂μ`. The factor $p$ is kept on both sides, so a cell of probability $0$ needs no separate case: both sides are $0$ (the set average then has Lean's default value $0$, multiplied by $p = 0$). The left side is the extended real `∫⁻_S g⁺ dμ − ∫⁻_S g⁻ dμ` in `EReal`; conclusion 1 is what makes this subtraction the book's value.
--
--   Differences from the source:
--   - encoding: a random vector ξ with distribution P → a probability measure μ on EuclideanSpace ℝ (Fin N), ξ the identity; reason: both sides depend only on the law of ξ
--   - encoding: E[ξ | S^l] exists (presupposed by the book) → hypothesis Integrable (fun ξ => ξ) μ; reason: the conditional means of the cells of a finite partition exist exactly when ξ has a finite mean
--   - encoding: p^l E[g(x,ξ) | S^l] ≥ p^l g(x, E[ξ | S^l]) for a cell with P[ξ ∈ S^l] > 0 → ∫_S g ≥ μ.real S · g(⨍ ξ in S, ξ ∂μ) for every measurable S; reason: p^l E[g | S^l] = ∫_{S^l} g by definition, and a cell of probability 0 makes both sides 0
--   - reading: g(x,·) convex → g : ℝ^N → ℝ real-valued and convex on a convex set C with μ(Cᶜ) = 0 (values outside C unconstrained); reason: the book's convex functions may take the value +∞ (Section 2.11, printed p. 98, PDF p. 124); C = ℝ^N is a finite convex function on ℝ^N, C = dom g covers a proper convex integrand finite almost surely, and integrands such as 1/ξ or −log ξ of a positive ξ are included; an integrand equal to +∞ with positive probability has E = +∞, where the bound is immediate
--   - encoding: ∫_{S^l} g, possibly +∞ → EReal value ∫⁻_S g⁺ − ∫⁻_S g⁻ together with the conclusion ∫⁻_S g⁻ ≠ ∞; reason: this is the book's value in (−∞, +∞]; the clause rules out the undefined ∞ − ∞
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 8, §8.2, proof of Theorem 1, eq. (2.2), last inequality, printed p. 346 (PDF p. 365): "Σ_l p^l E[g(x,ξ) | S^l] ≥ Σ_l p^l g(x, E[ξ | S^l]), where the last inequality follows from Jensen's inequality"

import Mathlib
open MeasureTheory

namespace StochasticProg.PartitionJensen

/-- **Jensen's inequality on one cell — (2.2), last step.**
Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, Chapter 8,
§8.2, proof of Theorem 1, eq. (2.2), printed p. 346 (PDF p. 365): termwise,
`p^l E[g(x,ξ) | S^l] ≥ p^l g(x, E[ξ | S^l])`, "where the last inequality follows from Jensen's
inequality".

Let `μ` be the law of `ξ` in `ℝ^N`, with a finite mean, let `s` be a measurable cell with
probability `p = P[ξ ∈ s]` and conditional mean `ξ_s = E[ξ | s]`, and let `g` be convex on a
convex set `C` that carries `ξ` (`μ Cᶜ = 0`). Then the negative part of `g` has finite integral over `s`, so
`∫_s g dμ = p · E[g(ξ) | s] ∈ (-∞, +∞]` is well defined, and `∫_s g dμ ≥ p · g(ξ_s)`.

**Formalization Note.** `ℝ^N` is `EuclideanSpace ℝ (Fin N)`. `p` is `μ.real s` and `ξ_s` is the
set average `⨍ ξ in s, ξ ∂μ`. The factor `p` is multiplied through, so a cell of probability
`0` needs no separate case: both sides are `0` (the set average then has Lean's junk value `0`,
multiplied by `p = 0`). `∫_s g dμ` is the extended real `∫⁻_s g⁺ − ∫⁻_s g⁻`; the first
conclusion makes the subtraction the book's value. "Convex" is read as real-valued and convex
on a convex set `C` of full measure (values outside `C` are unconstrained); `C = univ` is a
finite convex function on `ℝ^N`. No measurability of `g` is assumed. -/
theorem cell_jensen {N : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [IsProbabilityMeasure μ]
    (hξ : Integrable (fun ξ => ξ) μ)
    (s : Set (EuclideanSpace ℝ (Fin N))) (hs : MeasurableSet s)
    (C : Set (EuclideanSpace ℝ (Fin N))) (hCμ : μ Cᶜ = 0)
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (hg : ConvexOn ℝ C g) :
    (∫⁻ ξ in s, ENNReal.ofReal (-g ξ) ∂μ) ≠ ⊤ ∧
      ((μ.real s * g (⨍ ξ in s, ξ ∂μ) : ℝ) : EReal) ≤
        ((∫⁻ ξ in s, ENNReal.ofReal (g ξ) ∂μ : ENNReal) : EReal) -
          ((∫⁻ ξ in s, ENNReal.ofReal (-g ξ) ∂μ : ENNReal) : EReal) := by sorry

end StochasticProg.PartitionJensen
