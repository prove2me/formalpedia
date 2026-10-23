-- Prove2me | Theorems.Thm_TradingNetFlow_ChainStable_theorem_4_1
-- name    : TradingNetFlow.ChainStable.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:30.977962+00:00
-- url     : https://prove2.me/theorems/a40b71fd-2bd5-42c4-8800-18917a7287cc
-- title:
--   Theorem 4.1, PDF p. 11 — a competitive equilibrium exists
-- statement:
--   Let $G=(N,E)$ be a trading network with finitely many agents and trades, in which every trade has distinct seller and buyer and every valuation $w_i$ is M$^\natural$-concave in the signed representation. Then there exist an outcome $X\subseteq E$ and a price vector $p\in\mathbb R^E$ such that $(X,p)$ is a competitive equilibrium:
--   $$X\cap\delta(i)\in D_i(p)=\operatorname{arg\,max}\{u_i(Y,p):Y\subseteq\delta(i)\}\qquad\text{for all } i\in N.$$
--
--   This is Theorem 1 of Hatfield, Kominers, Nichifor, Ostrovsky and Westkamp (2013), which the paper recovers from the optimality conditions of an M-convex submodular flow problem. In the proof of Theorem 5.8 it is applied to the contraction of the economy.
-- source:
--   Candogan, Epitropou & Vohra, Competitive Equilibrium and Trading Networks: A Network Flow Approach, IHS Economics Series Working Paper 323 (Aug. 2016), PDF p. 11, Theorem 4.1

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model

namespace TradingNetFlow.ChainStable

open Finset

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

theorem theorem_4_1 (G : Economy N E) (hG : G.Standing) :
    ∃ (X : Finset E) (p : E → ℝ), G.IsCompetitiveEquilibrium X p := by sorry

end TradingNetFlow.ChainStable
