-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_Supplement_lemma_D_4
-- name    : TransparencyTeamContracts.Submodular.Supplement.lemma_D_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:16:38.634084+00:00
-- url     : https://prove2.me/theorems/f32890b6-f673-4299-a27b-5f7e3b288fa3
-- title:
--   Lemma D.4 (used in the proof of Theorem 4.4) — Simultaneous pruning with comparison tolerance
-- statement:
--   Let $f$ be nonnegative, monotone and submodular, with nonnegative costs. Suppose $S$ contains only positive-cost agents, $0<W(S)\le1$, $0<\xi<1$, and
--   $$(2+\xi^{-1})\sum_{i\in S}w_i^2\le\xi^2/2.$$
--   Run the fixed-order simultaneous-pruning procedure, allowing every potential-comparison bias $e_i$ with $|e_i|\le\xi^2/(2n)$. Its output $T\subseteq S$ has recorded shares in $[0,1]$, zero shares outside $T$, and incentive support in the final team, satisfying
--   $$\sum_{i\in T}\alpha_i\le W(S)+\xi,\qquad f(T)\ge f(S)-W(T)(1-W(T)/W(S))-3\xi.$$
--   Its cached reward equals $f(T)$ and its query transcript has exactly $|S|+1$ entries. Shares are processing-time snapshots. No total-share-at-most-one claim is added; the stated bound may exceed one.
--
--   Differences from the source:
--   - encoding: finite agents and states with real data and operational optimal utilities → Fin indices and the published base game, simplex prior and operational suprema; reason: finite relabeling preserves every source instance; nonempty bounded payoff sets give the same optimal values, with no zero-cost or positive-baseline restriction
--   - encoding: deterministic quadratic-potential deletion with additive comparison error at most xi^2/(2n) → the explicit fixed-order procedure, universally quantified bounded comparison biases, and its cached-reward query list; reason: the chosen potential is within the permitted additive tolerance for every such bias; the list records the initial query and one new marginal query per processed agent
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Lemma D.4, printed p. 38 (PDF p. 40)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_SimultaneousPruning

open Finset

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Lemma D.4, printed 38 / PDF 40. Uniform over all allowed comparison errors. -/
theorem lemma_D_4 {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (hf : IsTechnology f) (hc : ∀ i, 0 ≤ c i) (S : Finset (Fin n))
    (hcost : ∀ i ∈ S, 0 < c i) (hW : 0 < W c S) (hW1 : W c S ≤ 1)
    (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hsmall : (2 + ξ⁻¹) * (∑ i ∈ S, weight c i ^ 2) ≤ ξ ^ 2 / 2)
    (e : Fin n → ℝ) (he : ∀ i, |e i| ≤ ξ ^ 2 / (2 * (n : ℝ))) :
    let out := simultaneousPrune f c S ξ e
    out.team ⊆ S ∧ SupportsOn f c out.shares out.team ∧
      (∀ i, i ∉ out.team → out.shares i = 0) ∧
      (∑ i ∈ out.team, out.shares i) ≤ W c S + ξ ∧
      f S - W c out.team * (1 - W c out.team / W c S) - 3 * ξ ≤ f out.team ∧
      out.reward = f out.team ∧ out.queries.length = S.card + 1 := by sorry

end TransparencyTeamContracts.Submodular.Supplement
