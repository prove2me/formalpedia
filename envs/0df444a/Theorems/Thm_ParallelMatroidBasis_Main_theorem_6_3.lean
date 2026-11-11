-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_theorem_6_3
-- name    : ParallelMatroidBasis.Main.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:13.909808+00:00
-- url     : https://prove2.me/theorems/c6d8179d-2ef9-4439-8495-20e010f3f66b
-- title:
--   Theorem 6.3 — $n^2$ runs of Algorithm 3 recover $\Omega(|S|/\log n)$ redundant elements with probability $\ge1-2^{-n}$
-- statement:
--   Let $n$ be sufficiently large. Let $M$ be a matroid and $S$ a subset of its ground set with $|S|\le n$, such that
--   $$\frac{\alpha(S)}{|S|}\le\frac1{100\log_2 n}\qquad\text{and}\qquad p_{x,M|S}\ge n^{-9}\ \text{ for every }x\in S,$$
--   where $\alpha(S)$ is the α-value and $p_{x,M|S}$ the probability that $x$ lies in the first circuit of a uniformly random ordering of $S$ in the restriction $M|S$.
--
--   There are an absolute constant $c>0$ and $n_0$ such that, for $n\ge n_0$ and all such $M,S$:
--   1. every run of Algorithm 3 on $S$ returns a set $R$ of **redundant** elements: $R\subseteq S$ and $R\subseteq\mathrm{span}(S\setminus R)$;
--   2. among $n^2$ independent runs of Algorithm 3 on $S$, with probability at least $1-2^{-n}$ at least one returns a set $R$ with
--   $$|R|\ \ge\ c\,\frac{|S|}{\log_2 n}.$$
--
--   Since each run makes all its queries in parallel, this deletes $\Omega(|S|/\log n)$ elements of $S$ in one round without changing the span; applied to the sets of the decomposition it gives the deletion step of the main algorithm.
--
--   **Formalization Note.** The $n^2$ independent runs are a uniformly random element of the finite product of $n^2$ copies of the seed space of Algorithm 3 (an $m$-subset $S'$ and $n^{21}$ orderings of $S'$).
--
--   Differences from the source:
--   - reading: a set R of redundant elements → R ⊆ S and R ⊆ span(S ∖ R), for every run; reason: the paper defines redundant elements of S_i as R_i ⊆ S_i with every x ∈ R_i in span(S_i ∖ R_i) (PDF p.24); Observation 6.1 shows every run satisfies it, so the clause is stated for every run
--   - encoding: with probability 1 − 2^{−n}; |R| = Ω(|S|/log n) → probability ≥ 1 − 2^{−n}; ∃ c > 0 chosen before n, M, S with |R| ≥ c|S|/log₂ n; reason: an Ω-bound is an absolute constant uniform over the instance; the probability is a lower bound
--   - encoding: n² independent trials of Algorithm 3 → the uniform distribution on Fin (n²) → Alg3Seed S m n^{21}; reason: a product of uniform distributions on finite sets is the uniform distribution on the product, i.e. independent trials
--   - encoding: §6.1 standing assumptions: n is a fixed ambient size parameter, at least the size of every set under consideration, and sufficiently large → ∃ n₀, ∀ n ≥ n₀, for every matroid M on any type and every finite S ⊆ E(M) with |S| ≤ n; reason: this is the section's own convention (PDF p.24) written as binders; the threshold n₀ is chosen before the matroid and the set
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Theorem 6.3, p.23 (PDF p.25), proof p.26 (PDF p.28); Observation 6.1 and the definition of redundant elements, p.22 (PDF p.24); standing assumptions of §6.1

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_Deletion

noncomputable section
open Classical

namespace ParallelMatroidBasis.Main

/-- Theorem 6.3, PDF p.25 (printed p.23), under the standing assumptions of §6.1. There are an
absolute constant `c > 0` and `n₀` such that for `n ≥ n₀` and every `M`, `S` as in Claim 6.4:
(1) every run of Algorithm 3 returns a set `R ⊆ S` of redundant elements, `R ⊆ span(S ∖ R)`;
(2) over `n²` independent runs of Algorithm 3, with probability at least `1 − 2^{−n}` at least one
run returns `R` with `|R| ≥ c |S| / log₂ n`. -/
theorem theorem_6_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (α : Type) (M : Matroid α) (S : Finset α),
        (↑S : Set α) ⊆ M.E → S.card ≤ n →
        (alphaVal M S : ℝ) / (S.card : ℝ) ≤ 1 / (100 * Real.logb 2 n) →
        (∀ x ∈ S, 1 / (n : ℝ) ^ 9 ≤ pMarg M S x) →
        (∀ ω : Alg3Seed S (mVal n S) (n ^ 21),
          alg3Run M S n ω ⊆ S ∧
            (↑(alg3Run M S n ω) : Set α) ⊆ M.closure (↑(S \ alg3Run M S n ω) : Set α)) ∧
        1 - 1 / (2 : ℝ) ^ n ≤
          ((Finset.univ.filter
              (fun ωs : Fin (n ^ 2) → Alg3Seed S (mVal n S) (n ^ 21) =>
                ∃ j, c * (S.card : ℝ) / Real.logb 2 n ≤ ((alg3Run M S n (ωs j)).card : ℝ))).card
              : ℝ) /
            (Fintype.card (Fin (n ^ 2) → Alg3Seed S (mVal n S) (n ^ 21)) : ℝ) := by sorry

end ParallelMatroidBasis.Main
