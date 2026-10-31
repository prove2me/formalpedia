-- Prove2me | Theorems.Thm_PersuasionNetworks_corollary_1
-- name    : PersuasionNetworks.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:07.033838+00:00
-- url     : https://prove2.me/theorems/aad179d4-524a-4d0f-b059-22db51d32187
-- title:
--   Corollary 1 (corrected: level only when $r$ is strict) — Algorithm 1 on an optimal solution of (OPT) gives an optimal mechanism
-- statement:
--   Suppose that Assumption 1 holds. Then an optimal solution to (OPT) satisfying C1–C4 exists. For every such solution $(p,z)$, Algorithm 1 has a run with a measurable signal map, and for every run and every signal map $f$ of it the deterministic mechanism $S=f(T)$ satisfies:
--
--   1. $S$ is consistent with $(p,z)$: $\mathbb P(S=k)=p_k$, $\mathbb E[T\cdot\mathbf 1\{S=k\}]=z_k$, and $\mathbb E[T\mid S=k]=z_k/p_k$ when $p_k>0$;
--   2. for $p_k>0$: $b_k\le z_k/p_k$ and $\nu(z_k/p_k)=r_k$;
--   3. if $r$ is strictly decreasing, then $z_k/p_k<b_{k-1}$ for $p_k>0$, so that $S$ is a level mechanism;
--   4. the designer's payoff is $\sum_kp_kr_k$;
--   5. $S$ is an optimal mechanism: for every signal space and every mechanism $\pi$ on it,
--   $$
--   \mathbb E\bigl[\nu(\mathbb E[T\mid S^\pi])\bigr]\le\mathbb E\bigl[\nu(\mathbb E[T\mid S])\bigr].
--   $$
--
--   This is the paper's main structural result: the infinite-dimensional problem of designing a public signal has a tight finite convex relaxation, and an optimal mechanism assigns at most two intervals of states to each signal.
--
--   Differences from the source:
--   - correction: "the level mechanism obtained using Algorithm 1" → S need not be a level mechanism; it is one when r is strictly decreasing, and in general ν(z_k/p_k) = r_k still holds; reason: Assumption 1 allows ties: for T uniform on [0, 1], K = 2, b = (1, 1/10, 0), r = (1, 1), p = (0, 1), z = (0, 1/2) is optimal with C1–C4 and signal 2 has posterior mean 1/2 ∉ [0, 1/10)
--   - generalization: an optimal solution with C1–C4 and the mechanism obtained from it are given → existence of the solution (Lemma 4) and of a run (Theorem 1), every run and every signal map, and the explicit payoff; reason: each added clause is implied by the page or used in its proof, and dropping them gives the printed claim
--   - encoding: Algorithm 1 → the relation IsAlgorithm1Run with IsSignalMap, free on the complement of the intervals; reason: that set is μ-null but may be nonempty, and a mechanism needs a signal at every state
--   - encoding: a mechanism π → a Markov kernel from ℝ into any measurable space S : Type u; reason: the family {π(·; t)} of p.10; states outside 𝒯 are μ-null
--   - encoding: E[T | S = s] → the mean of Mathlib's posterior κ†μ at s; reason: a version of the conditional expectation
--   - encoding: ν at a point outside 𝒯 → the junk value 0; reason: posterior means lie in 𝒯 almost surely
--   - encoding: the extended end points and F at them → EReal and extCdf; reason: footnote 24
--   - encoding: the index i ∈ [m] and the signal set → consecutive binding indices and ℕ with values in {1, …, K}; reason: same data
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Corollary 1, p.20

import Mathlib
import Definitions.Def_PersuasionNetworks_OPT
import Definitions.Def_PersuasionNetworks_Mechanism
import Definitions.Def_PersuasionNetworks_Algorithm1

open MeasureTheory ProbabilityTheory

universe u

namespace PersuasionNetworks

/-- **Corollary 1** (corrected), Candogan, SSRN 3346144 (preprint), p.20 (proof pp.20–21). Under Assumption 1:

1. (Lemma 4) an optimal solution to (OPT) satisfying C1–C4 exists;
2. for every such solution `(p, z)`, Algorithm 1 has a run with a measurable signal map (Theorem 1),
   and for every run and every signal map `f` of it, the deterministic mechanism `S = f(T)` is
   consistent with `(p, z)`, and
   * for `p_k > 0`: `b_k ≤ z_k / p_k`, and `ν(z_k / p_k) = r_k`;
   * if `r` is strictly decreasing, for `p_k > 0`: `z_k / p_k < b_{k-1}`, i.e. it is a level mechanism;
   * its payoff is `∑_k p_k r_k`;
   * it is an **optimal mechanism**: no mechanism, over any signal space, has a larger payoff.

**Formalization Note.** The page says "the level mechanism obtained using Algorithm 1 … is an optimal
mechanism". With ties in `r`, which Assumption 1 allows, the output need not be a level mechanism:
`T` uniform on `[0, 1]`, `K = 2`, `b = (1, 1/10, 0)`, `r = (1, 1)`, `p = (0, 1)`, `z = (0, 1/2)`. Signal `2`
has posterior mean `1/2 ∉ [0, 1/10)`, though the optimality claim stands. When `r` is strictly
decreasing the statement below contains the printed one. Clauses 1 and the existence of a run are
added so that the statement is not vacuous. -/
theorem corollary_1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ)
    (hμ : IsState μ 𝒯) (hstep : IsStepPayoff 𝒯 K b r) :
    (∃ p z, IsOptimal μ 𝒯 K b r p z ∧ SatisfiesC μ 𝒯 K p z) ∧
    ∀ p z, IsOptimal μ 𝒯 K b r p z → SatisfiesC μ 𝒯 K p z →
      (∃ (t' t'' : ℕ → EReal) (f : ℝ → ℕ), IsAlgorithm1Run μ 𝒯 K p z t' t'' ∧
        IsSignalMap μ 𝒯 K p z t' t'' f) ∧
      ∀ (t' t'' : ℕ → EReal) (f : ℝ → ℕ), IsAlgorithm1Run μ 𝒯 K p z t' t'' →
        ∀ hf : IsSignalMap μ 𝒯 K p z t' t'' f,
          IsConsistent μ K p z (Kernel.deterministic f hf.measurable) ∧
          (∀ k ∈ Finset.Icc 1 K, 0 < p k →
            b k ≤ ((z k / p k : ℝ) : EReal) ∧ nu K b r (z k / p k) = r k) ∧
          ((∀ k ∈ Finset.Icc 1 K, ∀ ℓ ∈ Finset.Icc 1 K, k < ℓ → r ℓ < r k) →
            ∀ k ∈ Finset.Icc 1 K, 0 < p k → ((z k / p k : ℝ) : EReal) < b (k - 1)) ∧
          designerPayoff μ (nu K b r) (Kernel.deterministic f hf.measurable) = objective K r p ∧
          ∀ (S : Type u) [MeasurableSpace S] (κ : Kernel ℝ S) [IsMarkovKernel κ],
            designerPayoff μ (nu K b r) κ ≤
              designerPayoff μ (nu K b r) (Kernel.deterministic f hf.measurable) := by sorry

end PersuasionNetworks
