-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_eq_5_7
-- name    : TokenQueue.ProductForm.eq_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:53.746015+00:00
-- url     : https://prove2.me/theorems/c496f8a0-53e8-4290-a8eb-b52dad424cf8
-- title:
--   Eqs. (5) and (7), p. 6 — φ(release) = φ(shift) = φ(x)+1, and the inserted token's holder leaves at rate η(φ(x)+1)(k(T1,…,Tk,T) − k(T1,…,Tk))
-- statement:
--   Let $x=(T_1,n_1,\dots,T_i,n_i)$ be a state of the token-based central queue, with $n_0=0$.
--
--   1. For a token $T\notin\{T_1,\dots,T_i\}$, $0\le k\le i$ and $0\le n\le n_k$, the state $\mathrm{release}_{k,n}(x,T)=(T_1,n_1,\dots,T_k,n_k-n,T,n,T_{k+1},n_{k+1},\dots,T_i,n_i)$ has one more customer than $x$, and the holder of $T$ (at position $k+1$) leaves it at rate
--   $$\mu_T(\mathrm{release}_{k,n}(x,T))=\eta(\phi(x)+1)\bigl(k(T_1,\dots,T_k,T)-k(T_1,\dots,T_k)\bigr).\tag{5}$$
--   2. For $1\le j\le i$, $0\le k\le j-1$ and $0\le n\le n_k$, the state $\mathrm{shift}_{k,n}(x,T_j)$ has one more customer than $x$, and the holder of $T_j$ (at position $k+1$) leaves it at rate
--   $$\mu_{T_j}(\mathrm{shift}_{k,n}(x,T_j))=\eta(\phi(x)+1)\bigl(k(T_1,\dots,T_k,T_j)-k(T_1,\dots,T_k)\bigr).\tag{7}$$
--
--   These are the departure rates that enter the release and shift terms of the global balance equations (8).
--
--   **Formalization Note** `shift` is the corrected predecessor state described in the definitions item (the printed one is mis-indexed for $k=0$ and $k=j-1$). $j$ is the paper's 1-based index (`j.val + 1` for `j : Fin i`).
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 6, Eqs. (5) and (7)

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm

open Finset

/-- Eqs. (5) and (7), p. 6: `φ(release_{k,n}(x,T)) = φ(shift_{k,n}(x,T_j)) = φ(x) + 1`, and the
customer holding the inserted token (position `k + 1`) leaves at rate
`η(φ(x)+1)(k(T₁,…,T_k,T) − k(T₁,…,T_k))`. -/
theorem eq_5_7 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (x : State T) :
    (∀ t : T, t ∉ toks x.1 → ∀ k ≤ x.1.length, ∀ n ≤ nAt x.1 k,
      phi (release x.1 k n t) = phi x.1 + 1 ∧
      muTok P (release x.1 k n t) k =
        P.eta (phi x.1 + 1) * (kfun P (pre x.1 k ++ [t]) - kfun P (pre x.1 k))) ∧
    (∀ j : Fin x.1.length, ∀ k ≤ j.val, ∀ n ≤ nAt x.1 k,
      phi (shift x.1 (j.val + 1) k n (x.1.get j).1) = phi x.1 + 1 ∧
      muTok P (shift x.1 (j.val + 1) k n (x.1.get j).1) k =
        P.eta (phi x.1 + 1) * (kfun P (pre x.1 k ++ [(x.1.get j).1]) - kfun P (pre x.1 k))) := by sorry

end TokenQueue.ProductForm
