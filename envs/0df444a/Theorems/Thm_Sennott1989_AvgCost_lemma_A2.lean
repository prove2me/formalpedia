-- Prove2me | Theorems.Thm_Sennott1989_AvgCost_lemma_A2
-- name    : Sennott1989.AvgCost.lemma_A2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:28.890957+00:00
-- url     : https://prove2.me/theorems/ecb2a7c3-c2a8-4163-b2a8-edef8686a84d
-- title:
--   Lemma A2 (p. 632) — lim sup_{α↑1} (1 − α)V_α(i) ≤ g_θ(i) for every policy θ
-- statement:
--   Consider a Markov decision chain on the states $0,1,2,\dots$ with nonnegative costs. For every policy $\theta$ (history-dependent and randomized allowed) and every state $i$,
--   $$\limsup_{\alpha\uparrow1}\,(1-\alpha)V_\alpha(i)\ \le\ g_\theta(i),\tag{A5}$$
--   where $V_\alpha(i)$ is the optimal $\alpha$-discounted cost and $g_\theta(i)$ the lim sup average cost of $\theta$ from $i$.
--
--   This Tauberian-type comparison gives the lower bound $g\le g_\theta(i)$ in the proof of the Theorem.
--
--   **Formalization Note** No assumption is made; both sides are in $[0,\infty]$ and may be infinite. The lim sup is taken as $\alpha\to1$ with $\alpha<1$.
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, Appendix, Lemma A2, (A5), p. 632

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott1989.AvgCost

open SennottDP.Discounted

/-- Sennott (1989), Appendix, Lemma A2, p. 632. If `θ` is any policy, then
`lim sup_{α↑1} (1 − α) V_α(i) ≤ g_θ(i)` for every state `i ≥ 0` (A5).

**Formalization Note** No assumption is made: `V_α(i)` and `g_θ(i)` lie in `[0, ∞]` and may be
infinite. `θ` ranges over all (history-dependent, randomized) policies. The lim sup is taken as
`α → 1` with `α < 1` (the filter `𝓝[<] 1` on `ℝ≥0`), in the complete lattice `[0, ∞]`. -/
theorem lemma_A2 {Act : Type} (M : MDC ℕ Act) (θ : Policy M) (i : ℕ) :
    limsup (fun α : ℝ≥0 => ((1 - α : ℝ≥0) : ℝ≥0∞) * valueFn M α i) (𝓝[<] 1) ≤
      SennottDP.SEN.avgCost M θ i := by sorry

end Sennott1989.AvgCost
