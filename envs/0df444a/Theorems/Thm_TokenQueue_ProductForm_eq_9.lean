-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_eq_9
-- name    : TokenQueue.ProductForm.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:47.502138+00:00
-- url     : https://prove2.me/theorems/26228cd1-078f-4f18-aeec-4f8c5759942e
-- title:
--   Eq. (9), p. 7 (proof of Theorem 1) — the weights (10) satisfy λπ((0)) = Σ_T µT((0,T))π((0,T))
-- statement:
--   Assume the standing assumptions and that $k$ is positive on non-empty sequences of distinct tokens, and let $w$ be the product-form weights (10), so that $w((0))=1$. Then the global balance equation (9) at the empty state holds:
--   $$\lambda\,w((0))=\sum_{T\in\mathcal T}\mu_T((T,0))\,w((T,0)),$$
--   where $(T,0)$ is the state with one customer, holding $T$, and $\mu_T((T,0))=\eta(1)s_1(T)$.
--
--   **Formalization Note** The paper writes the one-customer state as $(0,T)$. Uses (1) at $S=\emptyset$ and $\lambda_{\mathcal U(\emptyset)}=0$.
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 7, Eq. (9) and proof of Theorem 1 ('It is straightforward to show that (10) satisfies (9)')

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm

open Finset

/-- Eq. (9), p. 7, for the weights (10) (proof of Theorem 1, p. 7):
`λ π((0)) = ∑_{T ∈ 𝒯} µ_T((T,0)) π((T,0))`. -/
theorem eq_9 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (hk : KPos P) :
    lamTot P * weightL P [] = ∑ t, muTok P [(t, 0)] 0 * weightL P [(t, 0)] := by sorry

end TokenQueue.ProductForm
