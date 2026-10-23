-- Prove2me | Theorems.Thm_TradingNetFlow_ChainStable_corollary_5_6
-- name    : TradingNetFlow.ChainStable.corollary_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:42.841183+00:00
-- url     : https://prove2.me/theorems/29fae268-affd-4689-ab97-8b2b3674ddd1
-- title:
--   Corollary 5.6, PDF p. 15 — a minimal welfare-improving set of trades is a chain and, with suitable prices, blocks no trade
-- statement:
--   Let $G=(N,E)$ be a trading network in which every trade has distinct seller and buyer and every valuation $w_i$ is M$^\natural$-concave in the signed representation, and assume the no-trade outcome is inefficient. Let $T\subseteq E$ be a minimal set of trades that improves welfare, that is,
--   $$\sum_{i}w_i(\emptyset)<\sum_{i}w_i(T\cap\delta(i))\quad\text{and}\quad\sum_{i}w_i(T'\cap\delta(i))\le\sum_{i}w_i(\emptyset)\ \text{ for every } T'\subsetneq T.$$
--   Then
--   1. $T$ is a chain, and
--   2. there are prices $p^T$ such that $(T,p^T)$ is a blocking chain of the no-trade outcome. For every agent $i$ involved in $T$, every set in $i$'s demand restricted to the trades in $T$ at prices $p^T$ contains $T\cap\delta(i)$.
--
--   In the proof of Theorem 5.8 this corollary, applied to the contraction, produces the blocking chain that contradicts chain stability.
--
--   **Formalization Note.** The hypothesis that the no-trade outcome is inefficient is kept as on the page, although it follows from the existence of $T$. The blocking chain is stated for the outcome $X=\emptyset$, where the combined prices $p^{T\cup\emptyset}$ are just $p^T$.
-- source:
--   Candogan, Epitropou & Vohra, Competitive Equilibrium and Trading Networks: A Network Flow Approach, IHS Economics Series Working Paper 323 (Aug. 2016), PDF p. 15, Corollary 5.6 (i), (ii) and the minimality notion in the text before it

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model

namespace TradingNetFlow.ChainStable

open Finset

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

theorem corollary_5_6 (G : Economy N E) (hG : G.Standing) (h : ¬ G.IsEfficient ∅)
    (T : Finset E) (hT : G.welfare ∅ < G.welfare T)
    (hmin : ∀ T' ⊂ T, ¬ G.welfare ∅ < G.welfare T') :
    G.IsChain T ∧ ∃ pT : E → ℝ, G.IsBlockingChain ∅ pT T pT := by sorry

end TradingNetFlow.ChainStable
