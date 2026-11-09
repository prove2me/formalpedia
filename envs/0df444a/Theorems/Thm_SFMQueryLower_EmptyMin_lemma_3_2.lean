-- Prove2me | Theorems.Thm_SFMQueryLower_EmptyMin_lemma_3_2
-- name    : SFMQueryLower.EmptyMin.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:43.217205+00:00
-- url     : https://prove2.me/theorems/c4da1b2e-21c5-447a-8904-51c62db1f48f
-- title:
--   Lemma 3.2 — uniform expected count of queries stopping at each outer layer
-- statement:
--   There are absolute constants $c>0$ and $K\ge2$ such that for every even integer $k\ge K$, set $n=2k^2$. Let $A$ have error at most $1/3$ on each $f_b^\Pi$, for each bit $b$ and every equal-block partition $\Pi$ of $[n]$ with $|P_j|=|R_j|=k$. Sample such a partition uniformly and use an independent seed for $A$.
--
--   For every integer $i$ with $k/2\le i\le k$, run $A$ on $f_1^\Pi$ and let $Q_i$ count the actual queries with $\operatorname{stop}_\Pi(S)=i$. Then
--   $$\mathbb E_{\Pi,A}Q_i\ge c\sqrt n\log n.$$
--   The constants are independent of $k,A,i$. Repeated queries are counted, and infinite expectation is retained. This is the full rate used to charge the outer layers.
--
--   **Formalization Note** The expectation is the uniform finite average of seed expectations, which represents the independent product law. The asymptotic statement is asserted after a uniform threshold, as in Appendix B.1; no assertion at small even $k$ is intended.
--
--   Differences from the source:
--   - encoding: finite labeled ground sets and their subsets → Fin n and Finset (Fin n); reason: bijections relabel every finite source instance
--   - encoding: layers indexed from 1 and bits in {0,1} → blocks indexed by Fin k with Boolean slots, and Bool hidden bits; reason: source index j+1 corresponds to stored index j and false/true to 0/1
--   - encoding: internal randomized oracle interaction and expected queries → an arbitrary probability seed chooses a causal history strategy; costs are nonnegative extended series; reason: includes general measurable randomness and stopping, preserves infinite cost, and requires only observable-event measurability
--   - encoding: E Q_i = Omega(sqrt n log n) as even k grows with n=2k^2 → uniform existential c>0,K>=2 preceding k,A,i, and n computed as 2*k^2; reason: states the full source rate including its asymptotic threshold and every outer layer; even k makes natural k/2 exact
--   - encoding: stop is the minimum index above which all layers pass → stop is the largest failed source layer, with zero when no layer fails; reason: these are equal for every finite ordered partition, and each actual query has one stopping layer
--   - generalization: ordinary solving algorithms return answers almost surely → nonreturning runs are also allowed and counted as failures; reason: all almost surely halting source algorithms are included; the same indistinguishability and issue-count bounds apply to unsuccessful nonreturning runs
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Lemma 3.2, printed p. 10 / PDF p. 11; proof Appendix B.1, printed pp. 17–18 / PDF pp. 18–19

import Definitions.Def_SFMQueryLower_EmptyMin_LayerSampling

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin

/-- Fox, Lemma 3.2, printed p.10 / PDF p.11; proof Appendix B.1, pp.17–18.
One positive constant and one threshold work for every even `k`, algorithm and outer layer.
The finite partition average uses a seed law independent of the partition. -/
theorem lemma_3_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, 2 ≤ K ∧
      ∀ k : ℕ, K ≤ k → Even k →
      ∀ A : EmptyMinAlgorithm (2 * k ^ 2),
        (∀ π : EqualPartition k, ∀ b : Bool,
          CorrectOn A (1 / 3) (hardFunction π.val b)) →
        ∀ i : ℕ, k / 2 ≤ i → i ≤ k →
          ENNReal.ofReal (c * Real.sqrt (2 * (k : ℝ) ^ 2) *
            Real.log (2 * (k : ℝ) ^ 2)) ≤ averagedStoppingCount k A i := by sorry

end SFMQueryLower.EmptyMin
