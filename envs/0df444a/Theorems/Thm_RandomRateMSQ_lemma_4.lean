-- Prove2me | Theorems.Thm_RandomRateMSQ_lemma_4
-- name    : RandomRateMSQ.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:24:33.479446+00:00
-- url     : https://prove2.me/theorems/b2597eaa-775e-4ae1-9315-d87f57220ffc
-- title:
--   Lemma 4 — joint Skorokhod representation for countably many tight components
-- statement:
--   Let $S_1,S_2,\dots$ be Polish spaces and $\Xi^n=(X^n_1,X^n_2,\dots)$ random elements with $X^n_k\in S_k$, and suppose that $\{X^n_k\}_{n\in\mathbb N}$ is tight for each $k$. Then there are $n_1<n_2<\cdots$ and random variables $Y_{kj}\in S_k$ on one probability space $(\hat\Omega,\hat{\mathcal F},\hat P)$ such that
--
--   1. for each $j$, the family $(Y_{kj})_{k\in\mathbb N}$ has the same joint law as $(X^{n_j}_k)_{k\in\mathbb N}$;
--   2. for each $k$, $Y_{kj}$ converges almost surely as $j\to\infty$.
--
--   This extension of the Skorokhod representation theorem replaces the continuous mapping theorem in the proof of Theorem 5, where the limiting fairness process is only defined through its shifts.
--
--   **Formalization Note** Tightness of $\{X^n_k\}_n$: for every $\varepsilon>0$ there is a compact $K\subset S_k$ with $P(X^n_k\notin K)<\varepsilon$ for all $n$. Joint laws are laws on $\prod_kS_k$ with the product σ-algebra. Indices start at $0$.
--
--   Differences from the source:
--   - reading: random variables Y_{n_j} … taking values in S_{n_j} (garbled indices) → Y_{kj} ∈ S_k with (Y_{kj})_k distributed as (X^{n_j}_k)_k; reason: the printed indices do not type-check; this is the meaning the proof establishes and the use on p.18
--   - encoding: random elements, tight, Polish → measurable maps into Borel Polish spaces; tightness as ∀ε ∃ compact K ∀n P(Xⁿₖ ∉ K) < ε; joint law on the product σ-algebra; indices from 0; reason: Lean conventions; same instances
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, Lemma 4, p.17

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace RandomRateMSQ

/-- **Lemma 4** (Büke–Qin, arXiv:1905.04198v1, p.17), a joint Skorokhod representation: let
`S_k` be Polish spaces and `Ξⁿ = (Xⁿ₁, Xⁿ₂, …)` random elements with `Xⁿ_k ∈ S_k`, and suppose
`{Xⁿ_k}_{n∈ℕ}` is tight for each `k`. Then there are `n₁ < n₂ < ⋯` and random variables `Y_{k j}`
on one probability space `(Ω̂, F̂, P̂)`, `Y_{k j} ∈ S_k`, such that for each `j` the family
`(Y_{k j})_{k∈ℕ}` has the joint law of `(X^{n_j}_k)_{k∈ℕ}`, and for each `k`, `Y_{k j}` converges
almost surely as `j → ∞`.

**Formalization Note.** The printed indices are garbled ("Y_{n_j} … taking values in S_{n_j}");
the statement above is their evident meaning, the one the proof establishes. Tightness of a
sequence of laws: for every `ε > 0` a compact set carrying all but `ε` of each law. The joint law is
the law on the product `Π_k S_k` (product σ-algebra = Borel σ-algebra of the countable product).
`X n k` is `Xⁿ_k`, `Y j k` is `Y_{k j}`; indices start at `0`. -/
theorem lemma_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Type*) [∀ k, TopologicalSpace (S k)] [∀ k, PolishSpace (S k)]
    [∀ k, MeasurableSpace (S k)] [∀ k, BorelSpace (S k)]
    (X : ℕ → (k : ℕ) → Ω → S k) (hX : ∀ n k, Measurable (X n k))
    (htight : ∀ k, ∀ ε : ℝ, 0 < ε → ∃ K : Set (S k), IsCompact K ∧
      ∀ n, P {ω | X n k ω ∉ K} < ENNReal.ofReal ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh) (Y : ℕ → (k : ℕ) → Ωh → S k),
        IsProbabilityMeasure Ph ∧
        (∀ j, IdentDistrib (fun ω k => Y j k ω) (fun ω k => X (φ j) k ω) Ph P) ∧
        ∀ k, ∀ᵐ ω ∂Ph, ∃ y : S k, Tendsto (fun j => Y j k ω) atTop (𝓝 y) := by sorry

end RandomRateMSQ
