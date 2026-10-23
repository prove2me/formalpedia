-- Prove2me | Theorems.Thm_TradingNetFlow_ChainStable_contraction_mNaturalConcave
-- name    : TradingNetFlow.ChainStable.contraction_mNaturalConcave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:33.343491+00:00
-- url     : https://prove2.me/theorems/a9eb5536-7492-44e9-a65d-110b9ae4616b
-- title:
--   Eq. (6), PDF p. 16 — the contraction's valuations ŵ_i are M♮-concave
-- statement:
--   Let $G=(N,E)$ be a trading network satisfying the standing assumptions: every trade has distinct seller and buyer, and every valuation $w_i$ is M$^\natural$-concave in the signed representation (sold trades $+1$, bought trades $-1$). Fix any outcome $X\subseteq E$ and any prices $p^X$. In the contraction $G^X=(N,E\setminus X)$, agent $i$ has the valuation
--   $$\hat w_i(S)=\max_{Y\subseteq X\cap\delta(i)}\Big[w_i(S\cup Y)+\sum_{e\in Y\cap\delta^+(i)}p^X_e-\sum_{e\in Y\cap\delta^-(i)}p^X_e\Big],\qquad S\subseteq\delta(i)\setminus X.$$
--   Then, for every agent $i$, $\hat w_i$ is M$^\natural$-concave in the signed representation on $\delta(i)\setminus X$.
--
--   The paper derives this from closure properties of M$^\natural$-concave functions in Murota's book (Theorems 6.13(3,4) and 6.15(1)). It is what lets the results proved for an arbitrary trading network, in particular Theorems 4.1 and 4.3 and Corollary 5.6, be applied to the contraction in the proof of Theorem 5.8.
--
--   **Formalization Note.** Equivalently, the contraction satisfies the M$^\natural$ half of the standing assumptions. The other half, that seller and buyer differ, passes to the contraction directly because the contraction keeps the sellers and buyers of the remaining trades.
-- source:
--   Candogan, Epitropou & Vohra, Competitive Equilibrium and Trading Networks: A Network Flow Approach, IHS Economics Series Working Paper 323 (Aug. 2016), PDF p. 16, eq. (6) and the sentence following it

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model

namespace TradingNetFlow.ChainStable

open Finset

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

theorem contraction_mNaturalConcave (G : Economy N E) (hG : G.Standing) (X : Finset E)
    (pX : E → ℝ) (i : N) :
    DiscreteConvex.EconomicEquilibrium.MNaturalConcave ((G.contraction X pX).wSigned i) := by sorry

end TradingNetFlow.ChainStable
