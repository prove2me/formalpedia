-- Prove2me | Theorems.Thm_SennottDP_Fatou_generalized_fatou
-- name    : SennottDP.Fatou.generalized_fatou
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T12:29:42.828988+00:00
-- url     : https://prove2.me/theorems/b928c60a-47f6-4e5e-9a76-281f59e9dbd1
-- title:
--   Proposition A.2.5 (Generalized Fatou's Lemma) — approximating distributions on increasing sets
-- statement:
--   Assume:
--
--   1. $S$ is a countable set with a probability distribution $(P_j)_{j\in S}$;
--   2. $(S_N)$ is an increasing sequence of subsets of $S$ with $\bigcup_N S_N = S$;
--   3. for each $N$, $(P_j(N))_{j\in S_N}$ is a probability distribution on $S_N$, and $\lim_{N\to\infty}P_j(N) = P_j$ for every $j\in S$;
--   4. $u(j,N)$ is a function of $j\in S_N$ and $N$ with values in $[-L,\infty]$, for a finite constant $L\ge 0$.
--
--   Then
--   $$\liminf_{N\to\infty}\ \sum_{j\in S_N} P_j(N)\, u(j,N) \;\ge\; \sum_{j\in S} P_j\, \liminf_{N\to\infty} u(j,N). \tag{A.18}$$
--
--   Here both the distribution and its support vary with $N$. This is the Fatou inequality used when a countable-state model is approximated by a sequence of models whose transition laws converge pointwise.
--
--   **Formalization Note** Hypotheses 1–3 are the structure `ApproxDist P SN Q` of the definition item, with `Q N j` $=P_j(N)$. The bound $u\ge -L$ is required only on $S_N$; values of $u(j,N)$ for $j\notin S_N$ never enter. Sums are the weighted sum `wsum`, the one on the left with weights $P_j(N)$ on $S_N$ and $0$ off $S_N$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 277–278, Proposition A.2.5, Eq. (A.18)

import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Proposition A.2.5 (Generalized Fatou's Lemma), pp. 277–278, (A.18).
(i)–(iii) are `ApproxDist P SN Q` (`Q N j = P_j(N)`); (iv) `u(j, N) ∈ [−L, ∞]` for `j ∈ S_N`, with a
finite constant `L ≥ 0`. Then `liminf_N ∑_{j ∈ S_N} P_j(N) u(j, N) ≥ ∑_{j ∈ S} P_j liminf_N u(j, N)`. -/
theorem generalized_fatou {S : Type*} [Countable S] {P : S → ℝ≥0∞} {SN : ℕ → Set S}
    {Q : ℕ → S → ℝ≥0∞} (hA : ApproxDist P SN Q)
    (u : S → ℕ → EReal) (L : ℝ) (hL : 0 ≤ L) (hu : ∀ N, ∀ j ∈ SN N, ((-L : ℝ) : EReal) ≤ u j N) :
    wsum P (fun j => liminf (fun N => u j N) atTop) ≤
      liminf (fun N => wsum ((SN N).indicator (Q N)) (fun j => u j N)) atTop := by sorry

end SennottDP.Fatou
