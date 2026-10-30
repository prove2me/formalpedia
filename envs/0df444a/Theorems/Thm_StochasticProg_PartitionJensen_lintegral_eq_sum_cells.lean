-- Prove2me | Theorems.Thm_StochasticProg_PartitionJensen_lintegral_eq_sum_cells
-- name    : StochasticProg.PartitionJensen.lintegral_eq_sum_cells
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:43:18.764318+00:00
-- url     : https://prove2.me/theorems/1f1f9ae5-0def-4d93-ae5f-033ed309003e
-- title:
--   Chapter 8, eq. (2.2), first equality — an expectation is the sum of its integrals over the cells of a partition
-- statement:
--   Let $\mu$ be a measure on $\mathbb R^N$ and let $S^1, \dots, S^\nu \subseteq \mathbb R^N$ be measurable, pairwise disjoint sets whose union carries all of $\mu$, that is $\mu\big((S^1 \cup \dots \cup S^\nu)^{\mathrm c}\big) = 0$. Then for every function $f : \mathbb R^N \to [0, \infty]$,
--
--   $$
--   \int f(\xi)\, \mu(d\xi) \;=\; \sum_{l=1}^{\nu} \int_{S^l} f(\xi)\, \mu(d\xi),
--   $$
--
--   where both sides may be $+\infty$.
--
--   In the proof of Theorem 1 of §8.2 of Birge and Louveaux, the expectation $\mathrm E(g(x)) = \int_\Xi g(x,\xi)P(d\xi)$ is first written as $\sum_{l=1}^\nu \int_{S^l} g(x,\xi) P(d\xi)$ over a partition $\mathcal S^\nu = \{S^l\}$ of the support $\Xi$ (first equality of (2.2)). Applied to the positive part $g(x,\cdot)^+$ and the negative part $g(x,\cdot)^-$, this statement gives that decomposition without any integrability assumption.
--
--   **Formalization Note** $\mathbb R^N$ is `EuclideanSpace ℝ (Fin N)`, the index $l = 1, \dots, \nu$ is `Fin ν` (0-based), and the integrals are lower Lebesgue integrals `∫⁻`. Neither $f$ nor $\mu$ is restricted further: $f$ need not be measurable and $\mu$ need not be finite.
--
--   Differences from the source:
--   - generalization: the first equality of (2.2) for g(x,·) under the law P of ξ → the decomposition for every [0, ∞]-valued f under every measure μ; reason: applied to the positive and negative parts of g(x,·) under P it gives the book's equality by subtraction whenever the right side is defined
--   - generalization: S^ν a partition of the support Ξ → finitely many measurable, pairwise disjoint sets whose union has full measure; reason: a partition of Ξ is such a family because P(Ξ) = 1; the cells need not lie in Ξ
--   - encoding: cells S^l, l = 1, …, ν, implicitly measurable (P[ξ ∈ S^l] is used) → S : Fin ν → Set, MeasurableSet (S l); reason: 0-based index; measurability is presupposed by the book
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 8, §8.2, proof of Theorem 1, eq. (2.2), first equality, printed p. 346 (PDF p. 365): "E(g(x)) = Σ_{l=1}^ν ∫_{S^l} g(x,ξ)P(dξ)"

import Mathlib
open MeasureTheory

namespace StochasticProg.PartitionJensen

/-- **Decomposition of an expectation over a partition — (2.2), first equality.**
Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, Chapter 8,
§8.2, proof of Theorem 1, eq. (2.2), first equality, printed p. 346 (PDF p. 365):
`E(g(x)) = Σ_{l=1}^ν ∫_{S^l} g(x,ξ) P(dξ)`.

For a measure `μ` on `ℝ^N` and finitely many measurable, pairwise disjoint cells
`S l` (`l : Fin ν`) whose union has full measure, the (lower Lebesgue) integral of every
`[0, ∞]`-valued function `f` is the sum of its integrals over the cells. Applied to the
positive and the negative part of `g(x, ·)` this is the book's first equality in (2.2), with no
integrability assumption (both sides may be `∞`).

**Formalization Note.** `ℝ^N` is `EuclideanSpace ℝ (Fin N)`; the book's index `l = 1, …, ν`
is `Fin ν` (0-based). The book partitions the support `Ξ`; here the cells only need to cover a
set of full measure, which a partition of `Ξ` does since `P(Ξ) = 1`. `f` need not be measurable
and `μ` need not be finite. -/
theorem lintegral_eq_sum_cells {N ν : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin N)))
    (S : Fin ν → Set (EuclideanSpace ℝ (Fin N))) (hSm : ∀ l, MeasurableSet (S l))
    (hSd : Pairwise (Function.onFun Disjoint S)) (hSc : μ (⋃ l, S l)ᶜ = 0)
    (f : EuclideanSpace ℝ (Fin N) → ENNReal) :
    ∫⁻ ξ, f ξ ∂μ = ∑ l, ∫⁻ ξ in S l, f ξ ∂μ := by sorry

end StochasticProg.PartitionJensen
