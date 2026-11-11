-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_lemma_6_5
-- name    : ParallelMatroidBasis.Main.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:03.812916+00:00
-- url     : https://prove2.me/theorems/e587c914-6d77-4e0a-a280-e013892fc9bd
-- title:
--   Lemma 6.5 — spanning witnesses survive subsampling with probability $\Omega(1)$
-- statement:
--   Let $n$ be sufficiently large. Let $M$ be a matroid and $S$ a subset of its ground set with $|S|\le n$, such that
--   $$\frac{\alpha(S)}{|S|}\le\frac1{100\log_2 n}\qquad\text{and}\qquad p_{x,M|S}\ge n^{-9}\ \text{ for every }x\in S,$$
--   where $\alpha(S)$ is the α-value and $p_{x,M|S}$ the probability that $x$ lies in the first circuit of a uniformly random ordering of $S$ in the restriction $M|S$.
--
--   For $x\in S$ and an integer $g$ write $W_g(x)=\{T\in\binom{S-\{x\}}{g}:\mathrm{Ind}(T)=1,\ x\in\mathrm{span}(T)\}$ for the independent $g$-subsets of $S-\{x\}$ that span $x$. Put $m=\lceil(1-1/\log_2 n)|S|\rceil$. There is an absolute constant $c>0$ such that for every $x\in S$ there is an integer $g_x\le|S|/4$ for which a uniformly random $m$-element subset $S'\subseteq S-\{x\}$ satisfies
--   $$\Pr_{S'}\left[\frac{\big|W_{g_x}(x)\cap\binom{S'}{g_x}\big|}{\binom{m}{g_x}}\ \ge\ \frac1{2n^{10}}\right]\ \ge\ c .$$
--
--   After deleting a $1/\log n$ fraction of $S$ at random, the surviving elements still contain a dense family of independent sets spanning $x$ with constant probability. This is what makes $x$ "good" (Lemma 6.7) and hence detectable by Algorithm 3 (Claim 6.6).
--
--   Differences from the source:
--   - encoding: §6.1 standing assumptions: n is a fixed ambient size parameter, at least the size of every set under consideration, and sufficiently large → ∃ n₀, ∀ n ≥ n₀, for every matroid M on any type and every finite S ⊆ E(M) with |S| ≤ n; reason: this is the section's own convention (PDF p.24) written as binders; the threshold n₀ is chosen before the matroid and the set
--   - encoding: probabilities over uniformly random orderings and uniformly random subsets → ratios of counts over the finite types of orderings `Fin |S| ≃ S` and over `powersetCard`; reason: a uniform probability on a finite set is the fraction of its elements in the event
--   - encoding: Pr_{S′}[…] = Ω(1) → ∃ c > 0, chosen before n, M, S and x, with Pr_{S′}[…] ≥ c; reason: an Ω-bound is an absolute constant, uniform over the instance
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Lemma 6.5 and its proof, pp.24–25 (PDF pp.26–27); standing assumptions of §6.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_Deletion

noncomputable section
open Classical

namespace ParallelMatroidBasis.Main

/-- Lemma 6.5, PDF p.26 (printed p.24), under the standing assumptions of §6.1. There are an
absolute constant `c > 0` and `n₀` such that for `n ≥ n₀`, every `M` and `S` as in Claim 6.4 and
every `x ∈ S`, there is `g_x ≤ |S|/4` for which a uniformly random `S' ⊆ S − {x}` with
`m = ⌈(1 − 1/log₂ n)|S|⌉` elements satisfies
`Pr_{S'}[|{T ∈ (S−{x} choose g_x) : Ind(T)=1, x ∈ span(T)} ∩ (S' choose g_x)| / (m choose g_x)
≥ 1/(2n^{10})] ≥ c`. -/
theorem lemma_6_5 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (α : Type) (M : Matroid α) (S : Finset α),
        (↑S : Set α) ⊆ M.E → S.card ≤ n →
        (alphaVal M S : ℝ) / (S.card : ℝ) ≤ 1 / (100 * Real.logb 2 n) →
        (∀ x ∈ S, 1 / (n : ℝ) ^ 9 ≤ pMarg M S x) →
        ∀ x ∈ S, ∃ g : ℕ, (g : ℝ) ≤ (S.card : ℝ) / 4 ∧
          c ≤ ((((S.erase x).powersetCard (mVal n S)).filter
                (fun S' => (1 : ℝ) / (2 * (n : ℝ) ^ 10) ≤
                  ((witnesses M S x g ∩ S'.powersetCard g).card : ℝ) /
                    ((mVal n S).choose g : ℝ))).card : ℝ) /
              ((S.card - 1).choose (mVal n S) : ℝ) := by sorry

end ParallelMatroidBasis.Main
