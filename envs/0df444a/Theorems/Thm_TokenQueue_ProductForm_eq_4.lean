-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_eq_4
-- name    : TokenQueue.ProductForm.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:43.442323+00:00
-- url     : https://prove2.me/theorems/353fd1af-e2fb-4506-a786-fa274f43fed9
-- title:
--   Eq. (4), p. 5 — the total departure rate is µ(x) = η(φ(x)) k(T1,…,Ti)
-- statement:
--   In the token-based central queue the holder of token $T_j$ in state $x=(T_1,n_1,\dots,T_i,n_i)$ leaves at rate $\mu_{T_j}(x)=\eta(\phi(x))\,s_j(T_1,\dots,T_j)$, where $\phi(x)=i+\sum_j n_j$. The total departure rate $\mu(x)=\sum_{j=1}^i\mu_{T_j}(x)$ satisfies
--   $$\mu(x)=\eta(\phi(x))\,k(T_1,\dots,T_i),$$
--   where $k(T_1,\dots,T_i)=\sum_{j=1}^i s_j(T_1,\dots,T_j)$.
--
--   This is the form of the departure rate used in the partial balance equation (12).
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 5, Eq. (4)

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm

open Finset

/-- Eq. (4), p. 5: `µ(x) = η(φ(x)) k(T₁,…,T_i)`. -/
theorem eq_4 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (x : State T) :
    mu P x.1 = P.eta (phi x.1) * kfun P (toks x.1) := by sorry

end TokenQueue.ProductForm
