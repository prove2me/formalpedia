-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_claim_6_6
-- name    : ParallelMatroidBasis.Main.claim_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:05.318404+00:00
-- url     : https://prove2.me/theorems/5420df01-dffa-4787-b008-9c5ea6132685
-- title:
--   Claim 6.6 — every good element is caught by Algorithm 3 with probability $\ge1-2^{-n^2}$
-- statement:
--   Let $n$ be sufficiently large, $M$ a matroid, $S$ a subset of its ground set with $|S|\le n$, and $S'\subseteq S$ a subset of size $m=\lceil(1-1/\log_2 n)|S|\rceil$ (the subset drawn in line 2 of Algorithm 3). Fix any values $g_x$ and let $x$ be good with respect to $S'$: $x\in S-S'$ and $|W_{g_x}(x)\cap\binom{S'}{g_x}|/\binom m{g_x}\ge 1/(2n^{10})$, where $W_g(x)$ is the family of independent $g$-subsets of $S-\{x\}$ spanning $x$. Then, over the $n^{21}$ independent uniformly random orderings of $S'$ drawn by Algorithm 3,
--   $$\Pr\big[x\in R\big]\ \ge\ 1-2^{-n^2},$$
--   where $R$ is the output of Algorithm 3.
--
--   Goodness of $x$ is certified by the longest independent prefix of a random ordering of $S'$ spanning $x$; with $n^{21}$ orderings this happens at least once with overwhelming probability. Combined with Lemma 6.7 it shows that Algorithm 3 recovers many redundant elements (Theorem 6.3).
--
--   **Formalization Note.** The probability is over the $n^{21}$ orderings with $S'$ fixed, i.e. conditional on the subset drawn in line 2. The values $g_x$ are arbitrary, not only those given by Claim 6.4.
--
--   Differences from the source:
--   - generalization: x good w.r.t. S′ for the values g_x given by Claim 6.4 → x good w.r.t. S′ for an arbitrary choice of values g : α → ℕ; reason: the proof uses only the density condition defining goodness, never how g_x was chosen; the values of Claim 6.4 are a special case
--   - encoding: S′ ⊆ S is the subset chosen in Algorithm 3; probability over the algorithm's remaining randomness → for every S′ ⊆ S with |S′| = m, the probability over n^{21} uniform orderings of S′; reason: conditioning on the subset drawn in line 2 leaves exactly these independent orderings
--   - encoding: §6.1 standing assumptions: n is a fixed ambient size parameter, at least the size of every set under consideration, and sufficiently large → ∃ n₀, ∀ n ≥ n₀, for every matroid M on any type and every finite S ⊆ E(M) with |S| ≤ n; reason: this is the section's own convention (PDF p.24) written as binders; the threshold n₀ is chosen before the matroid and the set
--   - encoding: probabilities over uniformly random orderings and uniformly random subsets → ratios of counts over the finite types of orderings `Fin |S| ≃ S` and over `powersetCard`; reason: a uniform probability on a finite set is the fraction of its elements in the event
--   - generalization: S is the input of Algorithm 3, with α(S)/|S| ≤ 1/(100 log n) and p_{x,M|S} ≥ n^{−9} for every x ∈ S (§6.1) → no hypothesis on S beyond S ⊆ E(M) and |S| ≤ n; reason: the proof of Claim 6.6 uses only the goodness of x and the algorithm's orderings of S′, never the two input conditions; sets S satisfying them are a special case
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Claim 6.6 and its proof, p.25 (PDF p.27); definition of good elements, p.25 (PDF p.27); standing assumptions of §6.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_Deletion

noncomputable section
open Classical

namespace ParallelMatroidBasis.Main

/-- Claim 6.6, PDF p.27 (printed p.25), under the standing assumptions of §6.1. For `n`
sufficiently large, let `S` be a subset of the ground set of `M` with `|S| ≤ n` and let
`S' ⊆ S` be a subset of size `m = ⌈(1 − 1/log₂ n)|S|⌉` (the subset chosen in Algorithm 3). For
every choice of values `g` and every `x` good with respect to `S'`, `x` is in the output `R` of
Algorithm 3 with probability at least `1 − 2^{−n²}` over the `n^{21}` independent uniform
orderings of `S'`. -/
theorem claim_6_6 :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (α : Type) (M : Matroid α) (S S' : Finset α),
        (↑S : Set α) ⊆ M.E → S.card ≤ n → S' ⊆ S → S'.card = mVal n S →
        ∀ (g : α → ℕ) (x : α), IsGood M S n g S' x →
          1 - 1 / (2 : ℝ) ^ (n ^ 2) ≤
            ((Finset.univ.filter
                (fun πs : Fin (n ^ 21) → Ordering S' => x ∈ alg3Output M S S' (n ^ 21) πs)).card
                : ℝ) /
              (Fintype.card (Fin (n ^ 21) → Ordering S') : ℝ) := by sorry

end ParallelMatroidBasis.Main
