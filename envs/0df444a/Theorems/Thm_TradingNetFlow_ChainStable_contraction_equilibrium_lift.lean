-- Prove2me | Theorems.Thm_TradingNetFlow_ChainStable_contraction_equilibrium_lift
-- name    : TradingNetFlow.ChainStable.contraction_equilibrium_lift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:32.292999+00:00
-- url     : https://prove2.me/theorems/68430d74-ddbe-4056-b5cd-239b5848071e
-- title:
--   Proof of Theorem 5.8, PDF p. 17 — an equilibrium (∅, p̂) of G^X lifts to the equilibrium (X, (p^X, p̂)) of G
-- statement:
--   Let $G=(N,E)$ be a trading network, $X\subseteq E$ an outcome with prices $p^X$ such that $(X,p^X)$ is individually rational, and $G^X$ the contraction with valuations $\hat w_i$ of eq. (6). Suppose $\hat p\in\mathbb R^{E\setminus X}$ is such that $(\emptyset,\hat p)$ is a competitive equilibrium of $G^X$. Define $p\in\mathbb R^E$ by
--   $$p_e=\begin{cases}p^X_e,&e\in X,\\ \hat p_e,&e\notin X.\end{cases}$$
--   Then $(X,p)$ is a competitive equilibrium of $G$: every agent $i$ demands $X\cap\delta(i)$ at prices $p$.
--
--   This is the closing step of the proof of Theorem 5.8.
--
--   **Formalization Note.** No M$^\natural$-concavity is assumed. Individual rationality is the only part of chain stability the step uses.
-- source:
--   Candogan, Epitropou & Vohra, Competitive Equilibrium and Trading Networks: A Network Flow Approach, IHS Economics Series Working Paper 323 (Aug. 2016), PDF p. 17, proof of Theorem 5.8

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model

namespace TradingNetFlow.ChainStable

open Finset

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

theorem contraction_equilibrium_lift (G : Economy N E) (X : Finset E) (pX : E → ℝ)
    (hIR : G.IsIndividuallyRational X pX) (pHat : {e : E // e ∉ X} → ℝ)
    (hCE : (G.contraction X pX).IsCompetitiveEquilibrium ∅ pHat) :
    G.IsCompetitiveEquilibrium X (fun e => if h : e ∈ X then pX e else pHat ⟨e, h⟩) := by sorry

end TradingNetFlow.ChainStable
