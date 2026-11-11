-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_claim_6_4
-- name    : ParallelMatroidBasis.Main.claim_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:38.504248+00:00
-- url     : https://prove2.me/theorems/f2e6f5fb-4646-4cfe-b11f-f06cd317462c
-- title:
--   Claim 6.4 — dense spanning witnesses: some $g_x\le|S|/4$ with $|W_{g_x}(x)|/\binom{|S|-1}{g_x}\ge n^{-10}$
-- statement:
--   Let $n$ be sufficiently large. Let $M$ be a matroid and $S$ a subset of its ground set with $|S|\le n$, such that
--   $$\frac{\alpha(S)}{|S|}\le\frac1{100\log_2 n}\qquad\text{and}\qquad p_{x,M|S}\ge n^{-9}\ \text{ for every }x\in S,$$
--   where $\alpha(S)$ is the α-value and $p_{x,M|S}$ the probability that $x$ lies in the first circuit of a uniformly random ordering of $S$ in the restriction $M|S$.
--
--   For $x\in S$ and an integer $g$ write $W_g(x)=\{T\in\binom{S-\{x\}}{g}:\mathrm{Ind}(T)=1,\ x\in\mathrm{span}(T)\}$ for the independent $g$-subsets of $S-\{x\}$ that span $x$. Then for every $x\in S$ there is an integer $g_x\le|S|/4$ such that
--   $$\frac{|W_{g_x}(x)|}{\binom{|S|-1}{g_x}}\ \ge\ n^{-10}.$$
--
--   An element with a non-negligible chance of lying in the first circuit has, at some prefix length at most $|S|/4$, a polynomially dense family of independent sets spanning it. Lemma 6.5 feeds this family into the density-preservation theorem.
--
--   **Formalization Note.** If $S$ is nonempty and independent, then $p_{x,M|S}=0$ and the hypothesis fails, so the default α-value of an independent set never enters. For $S=\emptyset$ the statement is vacuous.
--
--   Differences from the source:
--   - encoding: §6.1 standing assumptions: n is a fixed ambient size parameter, at least the size of every set under consideration, and sufficiently large → ∃ n₀, ∀ n ≥ n₀, for every matroid M on any type and every finite S ⊆ E(M) with |S| ≤ n; reason: this is the section's own convention (PDF p.24) written as binders; the threshold n₀ is chosen before the matroid and the set
--   - encoding: probabilities over uniformly random orderings and uniformly random subsets → ratios of counts over the finite types of orderings `Fin |S| ≃ S` and over `powersetCard`; reason: a uniform probability on a finite set is the fraction of its elements in the event
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Claim 6.4 and its proof, pp.23–24 (PDF pp.25–26); standing assumptions of §6.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_Deletion

noncomputable section
open Classical

namespace ParallelMatroidBasis.Main

/-- Claim 6.4, PDF p.25 (printed p.23), under the standing assumptions of §6.1 (`n` sufficiently
large and at least the size of every set considered). Let `S` be a subset of the ground set of
`M` with `|S| ≤ n`, `α(S)/|S| ≤ 1/(100 log₂ n)` and `p_{x,M|S} ≥ n^{−9}` for every `x ∈ S`. Then
for every `x ∈ S` there is `g_x ≤ |S|/4` with
`|{T ∈ (S−{x} choose g_x) : Ind(T) = 1, x ∈ span(T)}| / (|S|−1 choose g_x) ≥ n^{−10}`. -/
theorem claim_6_4 :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (α : Type) (M : Matroid α) (S : Finset α),
        (↑S : Set α) ⊆ M.E → S.card ≤ n →
        (alphaVal M S : ℝ) / (S.card : ℝ) ≤ 1 / (100 * Real.logb 2 n) →
        (∀ x ∈ S, 1 / (n : ℝ) ^ 9 ≤ pMarg M S x) →
        ∀ x ∈ S, ∃ g : ℕ, (g : ℝ) ≤ (S.card : ℝ) / 4 ∧
          1 / (n : ℝ) ^ 10 ≤
            ((witnesses M S x g).card : ℝ) / ((S.card - 1).choose g : ℝ) := by sorry

end ParallelMatroidBasis.Main
