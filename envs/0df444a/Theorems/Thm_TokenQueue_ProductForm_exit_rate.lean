-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_exit_rate
-- name    : TokenQueue.ProductForm.exit_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:44.515928+00:00
-- url     : https://prove2.me/theorems/516e658d-7fd1-4872-9ffd-1bda74039ade
-- title:
--   §4.1.1, p. 6 and §4.1.4, p. 7 — the total transition rate out of every state x is λ + µ(x)
-- statement:
--   In the token-based central queue, for every state $y$ the rates $q(y,x)$ of the forward transitions out of $y$ (arrivals and departures with the reclaiming of the freed token, §4.1) add up to
--   $$\sum_{x}q(y,x)=\lambda+\mu(y).$$
--
--   The arrivals contribute $\lambda$ by (1), and each departure contributes its rate $\mu_{T_j}(y)$, since the probabilities of the ways the freed token is reclaimed or released sum to one. This is the left-hand coefficient $\lambda+\mu(x)$ of the global balance equations (8).
--
--   **Formalization Note** Stated as `HasSum` over the state type, so the sum is finite and not a `tsum` junk value. The standing assumptions are used for $\lambda_{\mathcal U(\emptyset)}=0$.
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 6, §4.1.1 ('By virtue of (1), we conclude that the total arrival rate into the system in any given state equals λ') and p. 7, §4.1.4 ('the total departure rate from a state x is simply µ(x)')

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm

open Finset

/-- §4.1.1, p. 6 and §4.1.4, p. 7: the total rate out of every state `y` is `λ + µ(y)`. -/
theorem exit_rate {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (y : State T) :
    HasSum (fun x => rate P y x) (lamTot P + mu P y.1) := by sorry

end TokenQueue.ProductForm
