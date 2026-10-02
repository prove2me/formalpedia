-- Prove2me | Theorems.Thm_SennottDP_ChainASM_as_passage_cost_liminf
-- name    : SennottDP.ChainASM.as_passage_cost_liminf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T14:42:25.456986+00:00
-- url     : https://prove2.me/theorems/351c29fc-318a-441f-98b1-e93b74985209
-- title:
--   Proposition C.4.5 — expected first passage costs are lower semicontinuous along an AS
-- statement:
--   Let $(\Gamma_N)$ be an approximating sequence for the Markov chain with costs $\Gamma$ on a denumerable state space $S$, and let $G$ be a finite nonempty subset of $S$. Assume that $m_{iG}<\infty$ for some $i$ and that $m_{iG}(N)<\infty$ for sufficiently large $N$. Then
--   $$\liminf_{N\to\infty}c_{iG}(N)\ge c_{iG}.$$
--
--   This is the cost counterpart of Proposition C.4.2(iii): the expected cost of a first passage to $G$ in the limit chain is at most the limit inferior of the corresponding costs in the approximating chains.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 305, Proposition C.4.5

import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem as_passage_cost_liminf {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (AS : ApproxSeq Γ) (G : Finset S) (hG : G.Nonempty) (i : S)
    (hm : Γ.meanPassage (↑G : Set S) i < ⊤)
    (hmN : ∀ᶠ N in atTop, AS.meanPassageN (↑G : Set S) N i < ⊤) :
    Γ.passageCost (↑G : Set S) i ≤
      liminf (fun N => AS.passageCostN (↑G : Set S) N i) atTop := by sorry

end SennottDP.ChainASM
