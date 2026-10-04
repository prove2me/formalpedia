-- Prove2me | Theorems.Thm_SennottDP_Fatou_liminf_tsum_increasing_ge
-- name    : SennottDP.Fatou.liminf_tsum_increasing_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T11:53:31.378873+00:00
-- url     : https://prove2.me/theorems/c6d41b61-e121-49c4-ad6c-0d365ad53420
-- title:
--   Proposition A.1.8 — Fatou's inequality for sums over an increasing sequence of sets
-- statement:
--   Let $S$ be a countable set and $(S_N)$ an increasing sequence of subsets of $S$ with $\bigcup_N S_N = S$. Let $u(j,N)\in[0,\infty]$ be defined for $j\in S_N$ (or for all $j\in S$). Then
--   $$\liminf_{N\to\infty}\ \sum_{j\in S_N} u(j,N) \;\ge\; \sum_{j\in S}\ \liminf_{N\to\infty} u(j,N). \tag{A.6}$$
--
--   For fixed $j$, the lower limit on the right is meaningful because $j\in S_N$ for all sufficiently large $N$. The inequality fails for functions taking negative values (Example A.1.9). It is the form of Fatou's lemma needed when the state space is approximated by an increasing sequence of finite or countable sets.
--
--   **Formalization Note** $u$ is a function on all of $S$ with values in `ℝ≥0∞`; its values at $j\notin S_N$ never enter, because the sum over $S_N$ is written as the sum over $S$ of the indicator of $S_N$ times $u(\cdot,N)$, and the lower limit along $N\to\infty$ depends only on large $N$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 273–274, Proposition A.1.8, Eq. (A.6)

import Mathlib

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Proposition A.1.8, pp. 273–274, (A.6). `S` is countable, `(S_N)` is an
increasing sequence of subsets of `S` with `⋃_N S_N = S`, and `u(j, N) ∈ [0, ∞]` is a function of
`j ∈ S_N` and `N` (its values for `j ∉ S_N` are not used):
`liminf_N ∑_{j ∈ S_N} u(j, N) ≥ ∑_{j ∈ S} liminf_N u(j, N)`. -/
theorem liminf_tsum_increasing_ge {S : Type*} [Countable S] (SN : ℕ → Set S)
    (hmono : Monotone SN) (hunion : ⋃ N, SN N = Set.univ) (u : S → ℕ → ℝ≥0∞) :
    ∑' j, liminf (fun N => u j N) atTop ≤
      liminf (fun N => ∑' j, (SN N).indicator (fun i => u i N) j) atTop := by sorry

end SennottDP.Fatou
