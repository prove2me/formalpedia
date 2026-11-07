-- Prove2me | Theorems.Thm_SingleOrSample_theorem_4_1
-- name    : SingleOrSample.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:45.129204+00:00
-- url     : https://prove2.me/theorems/75edc49a-2241-4233-aeb9-159d8feb2c24
-- title:
--   Theorem 4.1 with Corollary 4.2 — the safe strategy gives each submodular agent $1/24$-MMS, with failure probabilities summing to at most $0.577$
-- statement:
--   Consider Algorithm 2 with parameter $k=4$, for any $n$ agents and $m$ goods, and take $c=6$, so the normalized target is $\tau=1/(ck)=1/24$. Write $\mathrm{MMS}_v$ for the maximin share of $v$ for $n$ bundles.
--
--   1. **(Theorem 4.1.)** There are numbers $q_i\ge0$, $i\in[n]$, with $\sum_iq_i\le0.577$, such that for every agent $i$ with a monotone, normalized, submodular valuation $v$, and every profile of legal strategies in which agent $i$ follows the safe strategy for $v$,
--   $$\Pr\Bigl[v(A_i)\ge\tfrac1{24}\mathrm{MMS}_v\Bigr]\ge1-q_i.$$
--   2. **(Corollary 4.2.)** If all agents have such valuations and all follow their safe strategies, then with probability at least $0.423$ the bundles $A_1,\dots,A_n$ are pairwise disjoint and $v_i(A_i)\ge\frac1{24}\mathrm{MMS}_{v_i}$ for all $i$. That is, Algorithm 2 is $(1/24,\,0.423)$-MMS competitive.
--
--   This is the first MMS guarantee for online agent arrivals with no information about the later agents. Part 1 is a guarantee to a single agent that holds whatever the other agents do, even if they know all valuations and watch all coins already tossed.
--
--   **Formalization Note** The strategy's target is $\frac1{24}\mathrm{MMS}_v$, on the scale of the unnormalized $v$. The safe predicate does not constrain an agent with $\mathrm{MMS}_v=0$, whose guarantee is $0\le v(A)$; such an agent may play any legal strategy.
--
--   Differences from the source:
--   - generalization: for every instance … the existence of failure probabilities q_i → q depends on n only, and precedes the agent, the valuation and the profile; reason: a q that works for all instances works for each instance; the page's proof gives this q
--   - generalization: Theorem 4.1 alone → clause 2 added from Corollary 4.2 (p.13), with the pairwise disjointness of the bundles; reason: the abstract's headline is the simultaneous form, and clause 1 gives only part of it
--   - encoding: regardless of the actions of the other agents, including randomized ones → every profile of legal deterministic history-dependent strategies; reason: a randomized profile is a mixture, and the bound passes through mixtures as q does not depend on the profile
--   - encoding: the safe strategy S_i with ties open → every strategy satisfying the predicate IsSafe; reason: the page's argmax and largest marginal values leave ties open
--   - encoding: normalized instance with τ = 1/24 → target (1/24)·MMS_v on the unnormalized v; reason: Appendix A: normalization rescales the target and does not change the strategy
--   - encoding: MMS_i = 0 agents can be simply ignored (footnote 3, p.30) → such an agent plays any legal strategy, unconstrained by IsSafe; reason: Algorithm 2 has no skip action, and every other agent's bound holds against any legal play
--   - encoding: allocation in Π_n([m]); B_ij ⊂ G → pairwise disjoint bundles (LittleCharity.EFX.IsPartialAllocation); B_ij ⊆ G; reason: by monotonicity leftovers may go to anyone without losing any bound; line 11 allows |G| = k(n − t)
--   - encoding: k = 4, c = 6 → k = 4 as a natural number, and c through the constant 1/24; reason: c occurs only through τ = 1/ck
--   - encoding: the rules of Algorithm 2 (e ∈ R_i, |B_ij| = k(n − t)) → every strategy, the agent's own included, satisfies Legal at every history with t < n; reason: the algorithm enforces these rules; a safe strategy's values where Legal and IsSafe could differ (buckets at histories where it takes a special round) never enter the law
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Theorem 4.1 and Corollary 4.2, p.13

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SingleOrSample_IsValuation
import Definitions.Def_SingleOrSample_runLaw
import Definitions.Def_SingleOrSample_IsSafe

namespace SingleOrSample

/-- **Theorem 4.1 with Corollary 4.2** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Theorem 4.1 and Corollary 4.2, p.13). In Algorithm 2 with
`k = 4` (and `c = 6`, so `τ = 1/24`), for all `n`, `m`:
1. there are `q_i ≥ 0` with `∑_i q_i ≤ 0.577` such that an agent `i` with a submodular valuation following the
   safe strategy gets at least `MMS_i / 24` with probability at least `1 − q_i`, against every legal profile of
   the others, whatever the agent's valuation;
2. if all agents have submodular valuations and follow safe strategies, then with probability at least
   `0.423` the bundles are pairwise disjoint and every agent gets at least `MMS_i / 24`.

**Formalization Note.** `q` depends on `n` only and precedes the agent, the valuation and the profile. A
strategy is a deterministic function of the full history; a randomized one is a mixture, covered since `q`
does not depend on the profile. The strategy's target is `τ = (1/24)·MMS v`, on the scale of the
unnormalized `v`; `IsSafe` does not constrain an agent with `MMS v = 0`, whose guarantee is `0 ≤ v(A)`.
Bundles need not exhaust the goods; by monotonicity the leftovers may go to anyone. Bundle sizes are `k(n − t)`
with `t` the special rounds at arrival. -/
theorem theorem_4_1 (n m : ℕ) :
    (∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i ≤ 0.577 ∧
      ∀ (i : Fin n) (v : Finset (Fin m) → ℝ), IsValuation v →
        SubsamplingSM.Offline.IsSubmodular v →
        ∀ σ : Fin n → Strategy m, (∀ j, Legal n 4 (σ j)) →
          IsSafe n 4 ((1 / 24) * LittleCharity.MMS.mms v n Finset.univ) v (σ i) →
          ENNReal.ofReal (1 - q i) ≤ (runLaw 4 σ n).toOuterMeasure
            {h | (1 / 24) * LittleCharity.MMS.mms v n Finset.univ ≤ v (allocOf h i)}) ∧
    (∀ vs : Fin n → Finset (Fin m) → ℝ,
      (∀ i, IsValuation (vs i) ∧ SubsamplingSM.Offline.IsSubmodular (vs i)) →
      ∀ σ : Fin n → Strategy m, (∀ j, Legal n 4 (σ j)) →
        (∀ i, IsSafe n 4 ((1 / 24) * LittleCharity.MMS.mms (vs i) n Finset.univ) (vs i) (σ i)) →
        ENNReal.ofReal 0.423 ≤ (runLaw 4 σ n).toOuterMeasure
          {h | LittleCharity.EFX.IsPartialAllocation (fun i : Fin n => (allocOf h i : Finset (Fin m))) ∧
            ∀ i, (1 / 24) * LittleCharity.MMS.mms (vs i) n Finset.univ ≤ vs i (allocOf h i)}) := by sorry

end SingleOrSample
