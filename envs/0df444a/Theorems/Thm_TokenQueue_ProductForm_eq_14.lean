-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_eq_14
-- name    : TokenQueue.ProductForm.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:57.48982+00:00
-- url     : https://prove2.me/theorems/bc94a146-a6c7-4adc-ac6a-5779aad37f4a
-- title:
--   Eq. (14), p. 8 (Appendix A, pp. 24–25) — the weights (10) satisfy λU({T1,…,Ti})π(x) = Σ_j Σ_{k<j} Σ_{n≤nk} µTj(shift_{k,n}(x,Tj)) s_{k,n}(x,Tj) π(shift_{k,n}(x,Tj)), shift corrected
-- statement:
--   Assume Conditions 1 and 2, the standing assumptions, and that $k$ is positive on non-empty sequences of distinct tokens, and let $w$ be the product-form weights (10). For every state $x=(T_1,n_1,\dots,T_i,n_i)$,
--   $$\lambda_{\mathcal U(\{T_1,\dots,T_i\})}\,w(x)=\sum_{j=1}^{i}\sum_{k=0}^{j-1}\sum_{n=0}^{n_k}\mu_{T_j}(\mathrm{shift}_{k,n}(x,T_j))\,s_{k,n}(x,T_j)\,w(\mathrm{shift}_{k,n}(x,T_j)),$$
--   with $n_0=0$, $s_{k,n}(x,T_j)=\beta_k(T_j)^n\beta_{k+1}(T_j)^{n_{k+1}}\cdots\beta_{j-1}(T_j)^{n_{j-1}}(1-\beta_{j-1}(T_j))$, and $\mathrm{shift}_{k,n}(x,T_j)$ the state from which a departure of the holder of $T_j$, followed by the reclaiming of $T_j$, leads to $x$: for $k+1<j$ it is $(T_1,n_1,\dots,T_k,n_k-n,T_j,n,T_{k+1},n_{k+1},\dots,T_{j-1},n_{j-1}+1+n_j,T_{j+1},\dots,T_i,n_i)$, and for $k=j-1$ it is $(T_1,n_1,\dots,T_{j-1},n_{j-1}-n,T_j,n+1+n_j,T_{j+1},\dots,T_i,n_i)$.
--
--   This partial balance equation matches the flow out of $x$ by arrivals that find no compatible token with the flow into $x$ by departures whose token is reclaimed.
--
--   **Formalization Note** The shift states are **corrected**: p. 6 defines them only for $1\le k$, $k+1<j$, while (8) and (14) sum over $0\le k\le j-1$, and the printed tuple is meaningless at $k=j-1$.
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 8, Eq. (14); proof in Appendix A, pp. 24–25; shift states p. 6

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm

open Finset

/-- Eq. (14), p. 8 (proved in Appendix A, pp. 24–25): under Conditions 1 and 2, the weights (10)
satisfy, for every state `x`,
`λ_{𝒰({T₁,…,T_i})} π(x) = ∑_{j=1}^{i} ∑_{k=0}^{j-1} ∑_{n=0}^{n_k}
  µ_{T_j}(shift_{k,n}(x,T_j)) s_{k,n}(x,T_j) π(shift_{k,n}(x,T_j))` (corrected `shift` states). -/
theorem eq_14 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P) (hk : KPos P)
    (x : State T) :
    lamU P (toks x.1).toFinset * weightL P x.1 =
      ∑ j : Fin x.1.length, ∑ k ∈ range (j.val + 1), ∑ n ∈ range (nAt x.1 k + 1),
        muTok P (shift x.1 (j.val + 1) k n (x.1.get j).1) k *
          sfac P x.1 (j.val + 1) k n (x.1.get j).1 *
          weightL P (shift x.1 (j.val + 1) k n (x.1.get j).1) := by sorry

end TokenQueue.ProductForm
