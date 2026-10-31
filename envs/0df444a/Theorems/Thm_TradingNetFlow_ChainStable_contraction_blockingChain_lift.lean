-- Prove2me | Theorems.Thm_TradingNetFlow_ChainStable_contraction_blockingChain_lift
-- name    : TradingNetFlow.ChainStable.contraction_blockingChain_lift
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:44.211728+00:00
-- url     : https://prove2.me/theorems/679c3716-c34a-483e-afae-fee922c7a5f8
-- title:
--   Proof of Theorem 5.8, PDF p. 17 — a blocking chain of ∅ in the contraction G^X blocks (X, p^X) in G
-- statement:
--   Let $G=(N,E)$ be a trading network, $X\subseteq E$ an outcome with prices $p^X$, and $G^X=(N,E\setminus X)$ the contraction with valuations $\hat w_i$ of eq. (6). Suppose $T\subseteq E\setminus X$ with prices $p^T$ is a blocking chain of the no-trade outcome in $G^X$. Then $T$, viewed as a set of trades of $G$, with prices $p^T$ on $T$ is a blocking chain of $(X,p^X)$ in $G$:
--   1. $T$ is a nonempty chain in $G$ and $T\cap X=\emptyset$;
--   2. for every agent $i$ involved in $T$ and every $Y^i\in D_i(p^{T\cup X})$, the demand restricted to $T\cup X$ at the combined prices,
--   $$T\cap\delta(i)\subseteq Y^i.$$
--
--   This is the step of the proof of Theorem 5.8 that transfers the blocking chain found in the contraction back to the original economy.
--
--   **Formalization Note.** The trades of $G^X$ are the subtype of trades not in $X$, and $T$ is mapped into $E$ by the inclusion. The price vector on $E$ is $p^T$ off $X$ and the arbitrary value $0$ on $X$; the latter is never read, since the combined prices use $p^X$ on $X$. No M$^\natural$-concavity is assumed.
-- source:
--   Candogan, Epitropou & Vohra, Competitive Equilibrium and Trading Networks: A Network Flow Approach, IHS Economics Series Working Paper 323 (Aug. 2016), PDF p. 17, proof of Theorem 5.8

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model

namespace TradingNetFlow.ChainStable

open Finset

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

theorem contraction_blockingChain_lift (G : Economy N E) (X : Finset E) (pX : E → ℝ)
    (T : Finset {e : E // e ∉ X}) (pT : {e : E // e ∉ X} → ℝ)
    (hT : (G.contraction X pX).IsBlockingChain ∅ pT T pT) :
    G.IsBlockingChain X pX (T.map (Function.Embedding.subtype _))
      (fun e => if h : e ∈ X then 0 else pT ⟨e, h⟩) := by sorry

end TradingNetFlow.ChainStable
