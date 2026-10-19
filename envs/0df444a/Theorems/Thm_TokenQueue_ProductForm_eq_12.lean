-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_eq_12
-- name    : TokenQueue.ProductForm.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:45.874074+00:00
-- url     : https://prove2.me/theorems/4eae8134-c433-4275-91ef-04a051c893e6
-- title:
--   Eq. (12), p. 7 (Appendix A, pp. 22–23) — the weights (10) satisfy µ(x)π(x) = 1{ni>0}λU π(…, ni − 1) + 1{ni=0}λTi({T1,…,Ti−1}) π(…, Ti−1, ni−1)
-- statement:
--   Let $w$ be the product-form weights (10) of the token-based central queue. For every state $x=(T_1,n_1,\dots,T_i,n_i)\ne(0)$,
--   $$\mu(x)w(x)=\mathbb 1_{\{n_i>0\}}\lambda_{\mathcal U(\{T_1,\dots,T_i\})}\,w(T_1,n_1,\dots,T_i,n_i-1)+\mathbb 1_{\{n_i=0\}}\lambda_{T_i}(\{T_1,\dots,T_{i-1}\})\,w(T_1,n_1,\dots,T_{i-1},n_{i-1}).$$
--
--   This partial balance equation matches the departure flow out of $x$ with the arrival flow into $x$; it is one of the three equations (12)–(14) whose sum, with (1), gives the global balance equations (8).
--
--   **Formalization Note** The page prints $\lambda_{T_i}(\{T_1,\dots,T_{i-1})$ with a missing brace. At $x=(0)$ both sides are $0$, so the statement is made for $x\ne(0)$. `KPos` and the standing assumptions ($\eta(j)>0$) make the weights' denominators non-zero; the equation is a property of the weights alone, and holds for any constant multiple $\pi=\pi((0))w$.
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 7, Eq. (12); proof in Appendix A, pp. 22–23

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm

open Finset

/-- Eq. (12), p. 7 (proved in Appendix A, pp. 22–23): for every state `x ≠ (0)`,
`µ(x)π(x) = 1{n_i>0} λ_{𝒰({T₁,…,T_i})} π(T₁,n₁,…,T_i,n_i − 1)
  + 1{n_i=0} λ_{T_i}({T₁,…,T_{i-1}}) π(T₁,n₁,…,T_{i-1},n_{i-1})` for the weights (10). -/
theorem eq_12 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (hk : KPos P) (x : State T) (hx : x.1 ≠ []) :
    mu P x.1 * weightL P x.1 =
      (if 0 < (x.1.getLast hx).2 then
        lamU P (toks x.1).toFinset * weightL P (modLast (· - 1) x.1) else 0) +
      (if (x.1.getLast hx).2 = 0 then
        lamTok P (pre x.1 (x.1.length - 1)).toFinset (x.1.getLast hx).1 *
          weightL P x.1.dropLast else 0) := by sorry

end TokenQueue.ProductForm
