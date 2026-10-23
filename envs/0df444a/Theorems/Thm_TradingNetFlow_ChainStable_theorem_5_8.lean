-- Prove2me | Theorems.Thm_TradingNetFlow_ChainStable_theorem_5_8
-- name    : TradingNetFlow.ChainStable.theorem_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:31.690543+00:00
-- url     : https://prove2.me/theorems/825bd5c2-2ad4-401c-9c94-548a41ddde0e
-- title:
--   Theorem 5.8, PDF p. 17 — every chain stable outcome (X, p^X) extends to a competitive equilibrium (X, p) with p = p^X on X
-- statement:
--   Let $G=(N,E)$ be a trading network with finitely many agents and trades, in which every trade has distinct seller and buyer and every valuation $w_i$ is M$^\natural$-concave in the signed representation (equivalently, every agent's preferences are fully substitutable). Suppose the outcome $X\subseteq E$ with prices $p^X$ is chain stable:
--   1. it is individually rational, $X\cap\delta(i)\in\operatorname{arg\,max}_{Y\subseteq X\cap\delta(i)}u_i(Y,p^X)$ for every agent $i$, and
--   2. no nonempty chain $Z$ with $Z\cap X=\emptyset$ and prices $p^Z$ blocks it, meaning that for every agent $i$ involved in $Z$ every $Y^i\in D_i(p^{Z\cup X})$ contains $Z\cap\delta(i)$.
--
--   Then there is a price vector $p\in\mathbb R^E$ such that $(X,p)$ is a competitive equilibrium and
--   $$p_e=p^X_e\qquad\text{for all } e\in X.$$
--
--   Together with Theorem 5.7 (a competitive equilibrium is stable, hence chain stable), this shows that in trading networks with fully substitutable preferences all the stability notions of Hatfield et al. (2013) coincide with competitive equilibrium: the weakest one, chain stability, already implies the strongest.
-- source:
--   Candogan, Epitropou & Vohra, Competitive Equilibrium and Trading Networks: A Network Flow Approach, IHS Economics Series Working Paper 323 (Aug. 2016), PDF p. 17, Theorem 5.8

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model

namespace TradingNetFlow.ChainStable

open Finset

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

theorem theorem_5_8 (G : Economy N E) (hG : G.Standing) (X : Finset E) (pX : E → ℝ)
    (hX : G.IsChainStable X pX) :
    ∃ p : E → ℝ, G.IsCompetitiveEquilibrium X p ∧ ∀ e ∈ X, p e = pX e := by sorry

end TradingNetFlow.ChainStable
