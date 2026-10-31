-- Prove2me | Theorems.Thm_TradingNetFlow_ChainStable_theorem_4_3
-- name    : TradingNetFlow.ChainStable.theorem_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:31.604199+00:00
-- url     : https://prove2.me/theorems/58f0aa23-96b5-4d78-9e1f-f45c92335475
-- title:
--   Theorem 4.3, PDF p. 11 — second welfare theorem: equilibrium prices support every efficient outcome
-- statement:
--   Let $G=(N,E)$ be a trading network in which every trade has distinct seller and buyer and every valuation $w_i$ is M$^\natural$-concave in the signed representation. Let $(X,p)$ be a competitive equilibrium and let $X'\subseteq E$ be an efficient outcome, that is,
--   $$\sum_{i\in N}w_i(S\cap\delta(i))\le\sum_{i\in N}w_i(X'\cap\delta(i))\qquad\text{for all }S\subseteq E.$$
--   Then $(X',p)$ is also a competitive equilibrium.
--
--   This is the strong form of the second welfare theorem (Theorem 3 of Hatfield et al. 2013): competitive prices support every efficient outcome, not only the one they were found with. In the proof of Theorem 5.8 it is combined with Theorem 4.1 to show that, if no prices support the empty outcome of the contraction, the empty outcome is inefficient there.
-- source:
--   Candogan, Epitropou & Vohra, Competitive Equilibrium and Trading Networks: A Network Flow Approach, IHS Economics Series Working Paper 323 (Aug. 2016), PDF p. 11, Theorem 4.3

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model

namespace TradingNetFlow.ChainStable

open Finset

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

theorem theorem_4_3 (G : Economy N E) (hG : G.Standing) (X X' : Finset E) (p : E → ℝ)
    (hX : G.IsCompetitiveEquilibrium X p) (hX' : G.IsEfficient X') :
    G.IsCompetitiveEquilibrium X' p := by sorry

end TradingNetFlow.ChainStable
