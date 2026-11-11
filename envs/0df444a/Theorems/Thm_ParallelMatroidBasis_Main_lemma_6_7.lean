-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_lemma_6_7
-- name    : ParallelMatroidBasis.Main.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:15.355398+00:00
-- url     : https://prove2.me/theorems/6494fde5-0618-4593-a49d-58e6d53c697a
-- title:
--   Lemma 6.7 — many good elements in expectation: $\mathbb E_{S'}[X(S')]\ge C\,|S-S'|$
-- statement:
--   Let $n$ be sufficiently large. Let $M$ be a matroid and $S$ a subset of its ground set with $|S|\le n$, such that
--   $$\frac{\alpha(S)}{|S|}\le\frac1{100\log_2 n}\qquad\text{and}\qquad p_{x,M|S}\ge n^{-9}\ \text{ for every }x\in S,$$
--   where $\alpha(S)$ is the α-value and $p_{x,M|S}$ the probability that $x$ lies in the first circuit of a uniformly random ordering of $S$ in the restriction $M|S$.
--
--   Put $m=\lceil(1-1/\log_2 n)|S|\rceil$. There is an absolute constant $C>0$ and a choice of values $g_x\le|S|/4$ ($x\in S$) such that, for a uniformly random $m$-element subset $S'\subseteq S$ and $X(S')$ the number of elements of $S$ that are good with respect to $S'$,
--   $$\mathbb E_{S'}\big[X(S')\big]\ \ge\ C\cdot|S-S'|=C\,(|S|-m).$$
--
--   A constant fraction of the elements removed by the subsampling are good on average. With Claim 6.6 this gives Theorem 6.3.
--
--   **Formalization Note.** An element $x\in S$ is good with respect to $S'$ when $x\notin S'$ and $|W_{g_x}(x)\cap\binom{S'}{g_x}|/\binom m{g_x}\ge 1/(2n^{10})$, with $W_g(x)$ the independent $g$-subsets of $S-\{x\}$ spanning $x$ (PDF p.27). The expectation is the average of $X(S')$ over all $m$-subsets of $S$, and $|S-S'|=|S|-m$ for every such $S'$.
--
--   Differences from the source:
--   - encoding: §6.1 standing assumptions: n is a fixed ambient size parameter, at least the size of every set under consideration, and sufficiently large → ∃ n₀, ∀ n ≥ n₀, for every matroid M on any type and every finite S ⊆ E(M) with |S| ≤ n; reason: this is the section's own convention (PDF p.24) written as binders; the threshold n₀ is chosen before the matroid and the set
--   - encoding: probabilities over uniformly random orderings and uniformly random subsets → ratios of counts over the finite types of orderings `Fin |S| ≃ S` and over `powersetCard`; reason: a uniform probability on a finite set is the fraction of its elements in the event
--   - encoding: the values g_x of Claim 6.4 used in the definition of good elements; an absolute constant C → ∃ C > 0 chosen before n, M and S, and ∃ g : α → ℕ with g x ≤ |S|/4 for x ∈ S; reason: the source's g_x is a choice made by Claim 6.4; the constant is uniform over the instance
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Lemma 6.7 and its proof, p.26 (PDF p.28); definition of good elements, p.25 (PDF p.27); standing assumptions of §6.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_Deletion

noncomputable section
open Classical

namespace ParallelMatroidBasis.Main

/-- Lemma 6.7, PDF p.28 (printed p.26), under the standing assumptions of §6.1. There are an
absolute constant `C > 0` and `n₀` such that for `n ≥ n₀` and every `M`, `S` as in Claim 6.4
there is a choice of values `g_x ≤ |S|/4` (`x ∈ S`) for which, with `S' ⊆ S` uniformly random of
size `m = ⌈(1 − 1/log₂ n)|S|⌉` and `X(S')` the number of elements of `S` good with respect to
`S'`, `E_{S'}[X(S')] ≥ C · |S − S'| = C (|S| − m)`. -/
theorem lemma_6_7 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (α : Type) (M : Matroid α) (S : Finset α),
        (↑S : Set α) ⊆ M.E → S.card ≤ n →
        (alphaVal M S : ℝ) / (S.card : ℝ) ≤ 1 / (100 * Real.logb 2 n) →
        (∀ x ∈ S, 1 / (n : ℝ) ^ 9 ≤ pMarg M S x) →
        ∃ g : α → ℕ, (∀ x ∈ S, (g x : ℝ) ≤ (S.card : ℝ) / 4) ∧
          C * ((S.card : ℝ) - (mVal n S : ℝ)) ≤
            (∑ S' ∈ S.powersetCard (mVal n S), ((S.filter (IsGood M S n g S')).card : ℝ)) /
              (S.card.choose (mVal n S) : ℝ) := by sorry

end ParallelMatroidBasis.Main
