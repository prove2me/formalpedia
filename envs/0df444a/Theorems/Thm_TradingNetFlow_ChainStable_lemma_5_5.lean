-- Prove2me | Theorems.Thm_TradingNetFlow_ChainStable_lemma_5_5
-- name    : TradingNetFlow.ChainStable.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:25.470794+00:00
-- url     : https://prove2.me/theorems/8e319fe0-7fc4-435f-b93d-9569dc4c6181
-- title:
--   Lemma 5.5, PDF p. 13 — if the no-trade outcome is inefficient, some chain of trades improves welfare
-- statement:
--   Let $G=(N,E)$ be a trading network in which every trade has distinct seller and buyer and every valuation $w_i$ is M$^\natural$-concave in the signed representation. Suppose the no-trade outcome $\emptyset$ is not efficient. Then there is a chain $Z\subseteq E$, a nonempty set of distinct trades $e_1,\dots,e_m$ with $e_k^-=e_{k+1}^+$ for $k<m$, whose execution improves welfare:
--   $$\sum_{i\in N}w_i(\emptyset)<\sum_{i\in N}w_i(Z\cap\delta(i)).$$
--
--   The lemma shows that, under full substitutability, a welfare improvement over no trade can always be found among chains. Corollary 5.6 builds on it to produce a blocking chain.
-- source:
--   Candogan, Epitropou & Vohra, Competitive Equilibrium and Trading Networks: A Network Flow Approach, IHS Economics Series Working Paper 323 (Aug. 2016), PDF p. 13, Lemma 5.5

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model

namespace TradingNetFlow.ChainStable

open Finset

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

theorem lemma_5_5 (G : Economy N E) (hG : G.Standing) (h : ¬ G.IsEfficient ∅) :
    ∃ Z : Finset E, G.IsChain Z ∧ G.welfare ∅ < G.welfare Z := by sorry

end TradingNetFlow.ChainStable
