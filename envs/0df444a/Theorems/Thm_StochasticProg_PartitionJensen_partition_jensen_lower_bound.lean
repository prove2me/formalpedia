-- Prove2me | Theorems.Thm_StochasticProg_PartitionJensen_partition_jensen_lower_bound
-- name    : StochasticProg.PartitionJensen.partition_jensen_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:44:22.493613+00:00
-- url     : https://prove2.me/theorems/06d853ea-7dd1-4742-b073-a4c7eb4d3092
-- title:
--   Chapter 8, Theorem 1 — Jensen lower bound over a partition of the support, $\mathrm E(g(x)) \ge \sum_l p^l g(x,\xi^l)$
-- statement:
--   Let $\xi$ be a random vector in $\mathbb R^N$ with law $P$ and finite mean. Let $S^1, \dots, S^\nu \subseteq \mathbb R^N$ be measurable, pairwise disjoint cells whose union has probability one (for instance a partition $\mathcal S^\nu = \{S^l, l = 1, \dots, \nu\}$ of the support $\Xi$ of $\xi$), and write
--
--   $$
--   p^l = \mathrm P[\xi \in S^l], \qquad \xi^l = \mathrm E[\xi \mid S^l] \qquad (l = 1, \dots, \nu).
--   $$
--
--   Let $D$ be a set of decisions $x$ and $g(x, \cdot) : \mathbb R^N \to \mathbb R$ an integrand that, for every $x \in D$, is convex on a convex set $C_x$ that carries $\xi$, $P(C_x^{\mathrm c}) = 0$ (values outside $C_x$ are arbitrary; $C_x = \mathbb R^N$ is a finite convex integrand, $C_x = \operatorname{dom} g(x,\cdot)$ a proper convex integrand finite almost surely). Then for every $x \in D$:
--
--   1. the negative part of $g(x, \xi)$ has finite expectation, so $\mathrm E(g(x)) = \mathrm E_\xi[g(x,\xi)] = \int g(x,\xi)\,P(d\xi)$ is a well-defined element of $(-\infty, +\infty]$;
--   2. the Jensen lower bound (2.1) holds:
--
--   $$
--   \mathrm E(g(x)) \;\ge\; \sum_{l=1}^{\nu} p^l\, g(x, \xi^l) .
--   $$
--
--   This is Theorem 1 of §8.2 of Birge and Louveaux, the basic lower bounding result of discrete bounding approximations: the expectation of a convex integrand is bounded below by its expectation under the discrete distribution that puts mass $p^l$ on the conditional mean $\xi^l$ of each cell. In stochastic programming it bounds the expected recourse function $\mathcal Q(x)$ below by $\mathcal Q^\nu(x) = \sum_l p^l Q(x, \xi^l)$.
--
--   **Formalization Note** $\mathbb R^N$ is `EuclideanSpace ℝ (Fin N)`, $\xi$ is the identity map under its law $\mu$ (a probability measure), and the index $l = 1, \dots, \nu$ is `Fin ν` (0-based). $p^l$ is `μ.real (S l)` and $\xi^l$ is the set average `⨍ ξ in S l, ξ ∂μ`; on a cell of probability $0$ the average has Lean's default value $0$, but that term is multiplied by $p^l = 0$. $\mathrm E(g(x))$ is the extended real `∫⁻ g(x,·)⁺ dμ − ∫⁻ g(x,·)⁻ dμ` in `EReal`, and conclusion 1 is what makes this subtraction the book's value; $\mathrm E(g(x)) = +\infty$ is allowed. No measurability of $g(x,\cdot)$ is assumed (the integrals are lower Lebesgue integrals `∫⁻`).
--
--   Differences from the source:
--   - encoding: a random vector ξ with distribution P → a probability measure μ on EuclideanSpace ℝ (Fin N), ξ the identity; reason: §8.2 integrates against P(dξ) only, so only the law matters
--   - encoding: ξ^l = E[ξ | S^l] exists (presupposed by the book) → hypothesis Integrable (fun ξ => ξ) μ; reason: the conditional means of the cells of a finite partition of a full-measure set exist exactly when ξ has a finite mean
--   - generalization: S^ν a partition of the support Ξ → finitely many measurable, pairwise disjoint sets whose union has full measure; reason: a partition of Ξ is such a family because P(Ξ) = 1; the cells need not lie in Ξ
--   - encoding: cells S^l, l = 1, …, ν, implicitly measurable (p^l = P[ξ ∈ S^l] is used) → S : Fin ν → Set, MeasurableSet (S l); reason: 0-based index; measurability is presupposed by the book
--   - encoding: p^l, ξ^l (atoms of probability p^l > 0) → μ.real (S l) and ⨍ ξ in S l, ξ ∂μ for every l; reason: a cell of probability 0 contributes 0 to the sum whatever value ξ^l is given
--   - generalization: D, not defined before Theorem 1 → an arbitrary set D in an arbitrary type X; reason: covers every set the book may mean, including the effective domain {x : E(g(x)) < +∞} of §8.6
--   - reading: g(x,·) convex → g(x,·) : ℝ^N → ℝ real-valued and convex on a convex set C x with μ((C x)ᶜ) = 0 (values outside C x unconstrained); reason: the book's convex functions may take the value +∞ (Section 2.11, printed p. 98, PDF p. 124); C = ℝ^N is a finite convex function on ℝ^N, C = dom g covers a proper convex integrand finite almost surely, and integrands such as 1/ξ or −log ξ of a positive ξ are included; an integrand equal to +∞ with positive probability has E = +∞, where the bound is immediate
--   - encoding: E(g(x)), possibly +∞ → EReal value ∫⁻ g(x,·)⁺ − ∫⁻ g(x,·)⁻ together with the conclusion ∫⁻ g(x,·)⁻ ≠ ∞; reason: this is the book's expectation in (−∞, +∞]; the clause rules out the undefined ∞ − ∞
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 8, §8.2, Theorem 1, eq. (2.1), printed p. 346 (PDF p. 365): "Theorem 1. Suppose that g(x,·) is convex for all x ∈ D. Then E(g(x)) ≥ Σ_{l=1}^ν p^l g(x,ξ^l). (2.1)"; setting on the same page: E(g(x)) = E_ξ[g(x,ξ)] = ∫_Ξ g(x,ξ)P(dξ), S^ν = {S^l, l = 1,...,ν} a partition of Ξ, ξ^l = E[ξ | S^l], p^l = P[ξ ∈ S^l]; support Ξ: Section 2.4, printed p. 60 (PDF p. 86)

import Mathlib
open MeasureTheory

namespace StochasticProg.PartitionJensen

/-- **Chapter 8, Theorem 1 — Jensen lower bound over a partition of the support, eq. (2.1).**
Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, Chapter 8,
§8.2, Theorem 1, eq. (2.1), printed p. 346 (PDF p. 365): "Theorem 1. Suppose that g(x,·) is
convex for all x ∈ D. Then E(g(x)) ≥ Σ_{l=1}^ν p^l g(x, ξ^l)."
Setting (same page): `E(g(x)) = E_ξ[g(x,ξ)] = ∫_Ξ g(x,ξ) P(dξ)`, `S^ν = {S^l, l = 1, …, ν}` a
partition of the support `Ξ`, `ξ^l = E[ξ | S^l]`, `p^l = P[ξ ∈ S^l]`.

Let `μ` be the law of the random vector `ξ` in `ℝ^N`, with a finite mean, let
the cells `S l` (`l : Fin ν`) be measurable, pairwise disjoint cells whose union has probability one, and
let `g(x, ·)` be convex for every `x ∈ D`: real-valued and convex on a convex set `C x` that
carries `ξ` (`μ (C x)ᶜ = 0`). Then for every `x ∈ D` the negative part of
`g(x, ξ)` has finite expectation (so `E(g(x)) ∈ (-∞, +∞]` is well defined) and
`E(g(x)) ≥ Σ_l p^l g(x, ξ^l)`.

**Formalization Note.** `ℝ^N` is `EuclideanSpace ℝ (Fin N)`, `ξ` is the identity under its law
`μ`, and the index `l = 1, …, ν` is `Fin ν` (0-based). A partition of the support `Ξ` is a
special case of the cells here, since `P(Ξ) = 1`. `p^l` is `μ.real (S l)` and `ξ^l` is the set
average `⨍ ξ in S l, ξ ∂μ`; on a cell of probability `0` the average has Lean's junk value `0`,
but the term is multiplied by `p^l = 0`. `E(g(x))` is the extended real
`∫⁻ g(x,·)⁺ dμ − ∫⁻ g(x,·)⁻ dμ`; the first conclusion makes the subtraction the book's value,
and `E(g(x)) = +∞` is allowed (no integrability of `g(x, ξ)` is assumed). `D` is an arbitrary
subset of an arbitrary type `X` of first-stage decisions. "Convex" (the book's definition,
Section 2.11, printed p. 98, PDF p. 124, allows `±∞` values) is read as: real-valued and convex on a convex set `C x` with
`μ (C x)ᶜ = 0`; values outside `C x` are unconstrained. `C x = univ` is a finite convex function
on `ℝ^N`; `C x = dom g(x, ·)` covers a proper extended-valued integrand that is finite almost
surely; and integrands such as `1/ξ` or `-log ξ` for a positive `ξ` are included. No
measurability of `g(x, ·)` is assumed (the expectations are lower Lebesgue integrals). -/
theorem partition_jensen_lower_bound {N ν : ℕ} {X : Type*}
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [IsProbabilityMeasure μ]
    (hξ : Integrable (fun ξ => ξ) μ)
    (S : Fin ν → Set (EuclideanSpace ℝ (Fin N))) (hSm : ∀ l, MeasurableSet (S l))
    (hSd : Pairwise (Function.onFun Disjoint S)) (hSc : μ (⋃ l, S l)ᶜ = 0)
    (g : X → EuclideanSpace ℝ (Fin N) → ℝ) (D : Set X)
    (C : X → Set (EuclideanSpace ℝ (Fin N))) (hCμ : ∀ x ∈ D, μ (C x)ᶜ = 0)
    (hg : ∀ x ∈ D, ConvexOn ℝ (C x) (g x)) :
    ∀ x ∈ D,
      (∫⁻ ξ, ENNReal.ofReal (-g x ξ) ∂μ) ≠ ⊤ ∧
        ((∑ l, μ.real (S l) * g x (⨍ ξ in S l, ξ ∂μ) : ℝ) : EReal) ≤
          ((∫⁻ ξ, ENNReal.ofReal (g x ξ) ∂μ : ENNReal) : EReal) -
            ((∫⁻ ξ, ENNReal.ofReal (-g x ξ) ∂μ : ENNReal) : EReal) := by sorry

end StochasticProg.PartitionJensen
