-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_claim_5_6
-- name    : ParallelMatroidBasis.Main.claim_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:46.041024+00:00
-- url     : https://prove2.me/theorems/61a02b96-975b-455e-953a-8b03794976ba
-- title:
--   Claim 5.6 (deterministic form) — α-values grow along the peeling: $\alpha(S_j)\ge\mu+\sqrt{\mu\log n/16}$
-- statement:
--   Let $n$ be sufficiently large. Let $N$ be a matroid with finite ground set $E$, $|E|\le n$, and let $A,B\subseteq E$ be disjoint sets such that
--   1. $B$ is dependent;
--   2. $q_A>1-n^{-6}$, where $q_A$ is the probability that the first circuit $C_\pi$ of a uniformly random ordering $\pi$ of $E$ lies in $A$;
--   3. $\alpha(A)\ge 50$ and $\alpha(A)/|A|\le 1/2$;
--   4. $|A|\le 2|B|$.
--
--   Then, with $\mu=\alpha(A)\,|B|/|A|$,
--   $$\alpha(B)\ \ge\ \mu+\sqrt{\mu\cdot\frac{\log_2 n}{16}} .$$
--
--   In the paper $A=S_i$ and $B=S_j$ are sets peeled off by Algorithm 2 at iterations $i<j<k$ with $|S_i|\le 2|S_j|$, and $N$ is the remaining matroid $Q$ at the start of iteration $i$, in which $S_i$ is greedily optimal. The α-value per element of the peeled sets therefore grows at a definite rate, which bounds the number of sets per size class (Lemma 5.7).
--
--   **Formalization Note.** $\alpha(A)\ge 50$ already forces $A$ to be dependent (the Lean α-value of an independent set is $0$), so dependence of $A$ is not a separate hypothesis. "Sufficiently large $n$" is an existential threshold $n_0$ chosen before the matroid and the sets.
--
--   Differences from the source:
--   - generalization: with probability ≥ 1 − 2n·2^{−n}, for the sets S_i, S_j peeled off by Algorithm 2 (i < j < k, |S_i| ≤ 2|S_j|) → for every matroid N with |E(N)| ≤ n and all disjoint A, B ⊆ E(N), B dependent, with q_A > 1 − n^{−6}, α(A) ≥ 50, α(A)/|A| ≤ 1/2 and |A| ≤ 2|B| (deterministic); reason: the paper proves these properties of the sets peeled off by Algorithm 2 hold on its good event of probability ≥ 1 − 2n·2^{−n} (Claim 5.1 and the EstimateAlpha bound (4), pp.16–19, and the preprocessing α ≥ 50), and its proof then uses only them; Algorithm 2 calls RemoveSmallCircuits and EstimateAlpha from [KPS25], which the paper does not define, so the probabilistic wording cannot be formalized from this source. The Lean statement holds for every family of sets with these properties, in particular for the peeled sets on the good event, so it specializes to the source's claim there
--   - encoding: for sufficiently large n (§5) → ∃ n₀, ∀ n ≥ n₀; reason: the section's convention, with the threshold chosen before the matroid
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Claim 5.6 and its proof, pp.19–20 (PDF pp.21–22); standing assumptions of §5, p.15 (PDF p.17); properties of the peeled sets, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_CircuitStats

noncomputable section
open Classical

namespace ParallelMatroidBasis.Main

/-- Claim 5.6, PDF p.21 (printed p.19), in the deterministic form its proof establishes on the
paper's good event. For all sufficiently large `n`: let `N` be a matroid with finite ground set
`E`, `|E| ≤ n`, and let `A, B ⊆ E` be disjoint with `B` dependent, `q_A(N) > 1 − n^{−6}`,
`α(A) ≥ 50`, `α(A)/|A| ≤ 1/2` and `|A| ≤ 2|B|`. Then, with `μ = α(A)|B|/|A|`,
`α(B) ≥ μ + √(μ · log₂ n / 16)`. (`A = S_i`, `B = S_j`, `N` = the matroid `Q` at the start of
iteration `i` of Algorithm 2.) -/
theorem claim_5_6 :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (α : Type) (N : Matroid α) (E A B : Finset α),
        N.E = (↑E : Set α) → E.card ≤ n → A ⊆ E → B ⊆ E → Disjoint A B →
        ¬ N.Indep (↑B : Set α) →
        1 - 1 / (n : ℝ) ^ 6 < qVal N E A →
        50 ≤ alphaVal N A →
        (alphaVal N A : ℝ) / (A.card : ℝ) ≤ 1 / 2 →
        (A.card : ℝ) ≤ 2 * (B.card : ℝ) →
        (alphaVal N A : ℝ) * B.card / A.card +
            Real.sqrt ((alphaVal N A : ℝ) * B.card / A.card * Real.logb 2 n / 16) ≤
          (alphaVal N B : ℝ) := by sorry

end ParallelMatroidBasis.Main
