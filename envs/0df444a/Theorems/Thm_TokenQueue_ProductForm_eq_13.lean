-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_eq_13
-- name    : TokenQueue.ProductForm.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:44.865388+00:00
-- url     : https://prove2.me/theorems/88ffa864-0e3c-4a7e-b7c2-4aad1c231b88
-- title:
--   Eq. (13), p. 7 (Appendix A, pp. 23–24) — the weights (10) satisfy λT({T1,…,Ti})π(x) = Σ_k Σ_{n≤nk} µT(release_{k,n}(x,T)) r_{k,n}(x,T) π(release_{k,n}(x,T))
-- statement:
--   Assume Conditions 1 and 2, the standing assumptions, and that $k$ is positive on non-empty sequences of distinct tokens, and let $w$ be the product-form weights (10). For every state $x=(T_1,n_1,\dots,T_i,n_i)$ and every token $T\notin\{T_1,\dots,T_i\}$,
--   $$\lambda_T(\{T_1,\dots,T_i\})\,w(x)=\sum_{k=0}^{i}\sum_{n=0}^{n_k}\mu_T(\mathrm{release}_{k,n}(x,T))\,r_{k,n}(x,T)\,w(\mathrm{release}_{k,n}(x,T)),$$
--   with $n_0=0$, $\mathrm{release}_{k,n}(x,T)=(T_1,n_1,\dots,T_k,n_k-n,T,n,T_{k+1},\dots,T_i,n_i)$ and $r_{k,n}(x,T)=\beta_k(T)^n\beta_{k+1}(T)^{n_{k+1}}\cdots\beta_i(T)^{n_i}$, $\beta_k(T)=\lambda_{\mathcal U(\{T_1,\dots,T_k\})}/\lambda_{\mathcal U(\{T_1,\dots,T_k,T\})}$, $\beta_0(T)=0$.
--
--   This partial balance equation matches the flow out of $x$ by arrivals that claim $T$ with the flow into $x$ by departures that release $T$.
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 7, Eq. (13); proof in Appendix A, pp. 23–24

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm

open Finset

/-- Eq. (13), p. 7 (proved in Appendix A, pp. 23–24): under Conditions 1 and 2, the weights (10)
satisfy, for every state `x` and every token `T ∉ {T₁,…,T_i}`,
`λ_T({T₁,…,T_i}) π(x) = ∑_{k=0}^{i} ∑_{n=0}^{n_k} µ_T(release_{k,n}(x,T)) r_{k,n}(x,T) π(release_{k,n}(x,T))`. -/
theorem eq_13 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P) (hk : KPos P)
    (x : State T) (t : T) (ht : t ∉ toks x.1) :
    lamTok P (toks x.1).toFinset t * weightL P x.1 =
      ∑ k ∈ range (x.1.length + 1), ∑ n ∈ range (nAt x.1 k + 1),
        muTok P (release x.1 k n t) k * rfac P x.1 k n t * weightL P (release x.1 k n t) := by sorry

end TokenQueue.ProductForm
