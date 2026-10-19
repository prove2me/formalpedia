-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_eq_1
-- name    : TokenQueue.ProductForm.eq_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:37.59671+00:00
-- url     : https://prove2.me/theorems/f3075f12-5f6b-4684-b5bb-ce0788e686b5
-- title:
--   Eq. (1), p. 4 — for any assignment rule, λ − λ_U(S) = Σ_{t∉S} λ_t(S)
-- statement:
--   Consider the token-based central queue with arrival rates $\lambda_c>0$, compatibility sets $\mathcal T_c$ and a randomised assignment rule, and let $S\subseteq\mathcal T$ be any set of unavailable tokens. Then the rate of arrivals that claim a token immediately equals the total rate of claims of the individual available tokens:
--   $$\lambda-\lambda_{\mathcal U(S)}=\sum_{t\in\mathcal T\setminus S}\lambda_t(S).$$
--
--   Here $\lambda=\sum_c\lambda_c$, $\lambda_{\mathcal U(S)}$ is the arrival rate of types all of whose compatible tokens lie in $S$, and $\lambda_t(S)$ is the rate at which arrivals claim $t$. The identity holds for every assignment rule; it is what makes the total arrival rate out of every state equal to $\lambda$.
--
--   **Formalization Note** The standing assumptions (`Params.Standing`) supply that the assignment probabilities are non-negative, vanish off $\mathcal T_c\setminus S$ and sum to one on it when it is non-empty.
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 4, Eq. (1)

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm

open Finset

/-- Eq. (1), p. 4: for any set `S` of unavailable tokens,
`λ − λ_{𝒰(S)} = ∑_{t ∉ S} λ_t(S)`, whatever the assignment rule. -/
theorem eq_1 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (S : Finset T) :
    lamTot P - lamU P S = ∑ t ∈ univ \ S, lamTok P S t := by sorry

end TokenQueue.ProductForm
