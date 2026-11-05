-- Prove2me | Theorems.Thm_TwoStageMatch_opt_online_le_opt_offline
-- name    : TwoStageMatch.opt_online_le_opt_offline
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:24.289792+00:00
-- url     : https://prove2.me/theorems/7ffdc271-8559-4340-b2d3-cee8673a73fe
-- title:
--   Benchmarks (1), (2): $\mathsf{OPT}_{\mathrm{online}}\le\mathsf{OPT}_{\mathrm{offline}}$
-- statement:
--   On every instance:
--
--   1. for every first-stage matching $M_1$ with matched supplies $S_1$ and every realization $A\subseteq D_2$,
--   $$w(S_1)+\mathrm{Max\text{-}WeightMatch}^w(A,S\setminus S_1)\le\mathrm{Max\text{-}WeightMatch}^w(D_1\cup A,S),$$
--   since $M_1$ together with a matching between $A$ and $S\setminus S_1$ is a matching between $D_1\cup A$ and $S$;
--   2. consequently $\mathsf{OPT}_{\mathrm{online}}\le\mathsf{OPT}_{\mathrm{offline}}$.
--
--   This is the first inequality $\Gamma(\text{Algorithm 1},\mathsf{OPT}_{\mathrm{online}})\ge\Gamma(\text{Algorithm 1},\mathsf{OPT}_{\mathrm{offline}})$ of Theorem 1: the omniscient offline policy dominates every online policy.
--
--   Differences from the source:
--   - encoding: the graph G = (D, S, E) with D = D₁ ∪ D₂, matchings, the law of D̃₂ → D = D₁ ⊕ D₂, edges as a relation, matchings as Finsets of edges, x : D₁ → S → ℝ vanishing off the edges, the law of D̃₂ as the product weight Π_{i∈A} π_i Π_{i∉A} (1 − π_i) on Finset D₂; reason: Lean conventions; same instances
--   - reading: the first inequality of Theorem 1, printed only between the two Γ; the benchmarks (1), (2) in prose ("an omniscient offline policy") → OPT_online ≤ OPT_offline on every instance, with the pointwise inequality for every M₁ and A; reason: the paper does not display the per-instance inequality; it is what the Γ inequality rests on
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, §2, p.10, benchmarks (1) and (2); first inequality of Theorem 1, p.12

import Mathlib
import Definitions.Def_TwoStageMatch_Instance

namespace TwoStageMatch

/-- **`OPT_online ≤ OPT_offline`** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, benchmarks (1)
and (2), p.10; the first inequality of Theorem 1, p.12). On every instance:
1. for every first-stage matching `M₁` (supplies `S₁`) and every realization `A ⊆ D₂`,
   `w(S₁) + Max-WeightMatch^w(A, S \ S₁) ≤ Max-WeightMatch^w(D₁ ∪ A, S)`
   (`M₁ ∪ M₂` is a matching between `D₁ ∪ A` and `S`);
2. hence `OPT_online ≤ OPT_offline`. -/
theorem opt_online_le_opt_offline {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S]
    [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S] (I : Instance D₁ D₂ S) :
    (∀ M, IsFirstStageMatching I M → ∀ A : Finset D₂,
      twoStageWeight I M A ≤ maxWeightMatch I.E I.w (firstStage ∪ secondStage A) Finset.univ) ∧
    optOnline I ≤ optOffline I := by sorry

end TwoStageMatch
