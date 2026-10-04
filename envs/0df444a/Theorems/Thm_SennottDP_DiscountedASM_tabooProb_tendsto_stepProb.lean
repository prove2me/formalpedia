-- Prove2me | Theorems.Thm_SennottDP_DiscountedASM_tabooProb_tendsto_stepProb
-- name    : SennottDP.DiscountedASM.tabooProb_tendsto_stepProb
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T07:39:48.253217+00:00
-- url     : https://prove2.me/theorems/3db2a627-8692-4b6a-ab0c-815ff02607ab
-- title:
--   Lemma 4.7.2 — taboo probabilities converge to transition probabilities
-- statement:
--   Let $\Delta$ be an MDC with countable state space $S$, let $(S_N)_{N\ge N_0}$ be the state spaces of an approximating sequence for $\Delta$, and let $e$ be a stationary policy of $\Delta$. Write ${}_{N*}P^{(t)}_{ij}(e)$ for the taboo probability of going from $i$ to $j$ in $t$ steps under $e$ in $\Delta$ while avoiding $S-S_N$ at the intermediate steps, and $P^{(t)}_{ij}(e)$ for the $t$-step transition probability. Then
--   $$
--   \lim_{N\to\infty}{}_{N*}P^{(t)}_{ij}(e)=P^{(t)}_{ij}(e),\qquad i,j\in S,\ t\ge1.
--   $$
--
--   As $S_N$ grows to $S$, forbidding excursions outside $S_N$ costs less and less probability over any fixed number of steps. The lemma feeds Lemma 4.7.3.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 78, Lemma 4.7.2, equation (4.41)

import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC
import Definitions.Def_SennottDP_DiscountedASM_ApproxSeq
import Definitions.Def_SennottDP_DiscountedASM_tabooProb

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.DiscountedASM

/-- Lemma 4.7.2 (p. 78): for a stationary policy `e` of `M`,
`lim_{N→∞} _{N*}P^{(t)}_{ij}(e) = P^{(t)}_{ij}(e)` for `i, j ∈ S`, `t ≥ 1` (4.41), where the
taboo probability avoids `S - S_N` at the intermediate steps. -/
theorem tabooProb_tendsto_stepProb {S Act : Type} [Countable S] (M : MDC S Act)
    (Δs : ApproxSeq M) (e : S → Act) (he : ∀ i, e i ∈ M.A i) (i j : S) (t : ℕ) (ht : 1 ≤ t) :
    Tendsto (fun N => M.tabooProb (Δs.SN N) e t i j) atTop (𝓝 (M.stepProb e t i j)) := by sorry

end SennottDP.DiscountedASM
