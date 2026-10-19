-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_eq_8_9
-- name    : TokenQueue.ProductForm.eq_8_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:53.675418+00:00
-- url     : https://prove2.me/theorems/01f524fb-c58f-400b-85e3-f21741774301
-- title:
--   Eqs. (8)–(9), p. 7 — the inflow Σ_y π(y)q(y,x) into every state x equals the right-hand side of the global balance equations (shift states corrected)
-- statement:
--   Let $\pi$ be any real function on the states of the token-based central queue and $q$ the forward transition rates of §4.1. For every state $x=(T_1,n_1,\dots,T_i,n_i)\ne(0)$, the inflow into $x$ is
--   $$\begin{aligned}\sum_y\pi(y)q(y,x)={}&\mathbb 1_{\{n_i>0\}}\lambda_{\mathcal U(\{T_1,\dots,T_i\})}\pi(T_1,n_1,\dots,T_i,n_i-1)+\mathbb 1_{\{n_i=0\}}\lambda_{T_i}(\{T_1,\dots,T_{i-1}\})\pi(T_1,n_1,\dots,T_{i-1},n_{i-1})\\&+\sum_{T\in\mathcal T\setminus\{T_1,\dots,T_i\}}\sum_{k=0}^{i}\sum_{n=0}^{n_k}\mu_T(\mathrm{release}_{k,n}(x,T))\,r_{k,n}(x,T)\,\pi(\mathrm{release}_{k,n}(x,T))\\&+\sum_{j=1}^{i}\sum_{k=0}^{j-1}\sum_{n=0}^{n_k}\mu_{T_j}(\mathrm{shift}_{k,n}(x,T_j))\,s_{k,n}(x,T_j)\,\pi(\mathrm{shift}_{k,n}(x,T_j)),\end{aligned}$$
--   the right-hand side of (8); for $x=(0)$ it is $\sum_{T\in\mathcal T}\mu_T((T,0))\,\pi((T,0))$, the right-hand side of (9). Here $n_0=0$.
--
--   Together with the total exit rate $\lambda+\mu(x)$, this says that the global balance equations $\pi(x)\sum_y q(x,y)=\sum_y\pi(y)q(y,x)$ are exactly (8)–(9): it lists every predecessor of $x$ with its transition rate.
--
--   **Formalization Note** $\pi$ is extended by $0$ to descriptors with repeated tokens (`piExt`); none occurs on the right-hand side. `shift` is the corrected predecessor state (see the definitions item). The standing assumptions make the transitions of probability zero (a customer of the first portion passed over) carry rate zero.
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 7, §4.1.4, Eqs. (8) and (9)

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm

open Finset

/-- Eqs. (8)–(9), p. 7: for every function `π` on the states, the inflow
`∑_y π(y) q(y, x)` into `x` under the forward transition rates equals the right-hand side of
the global balance equation (8) (for `x ≠ (0)`) or (9) (for `x = (0)`), with the corrected
`shift` states. -/
theorem eq_8_9 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (π : State T → ℝ) (x : State T) :
    HasSum (fun y => π y * rate P y x) (balanceRHS P (piExt π) x.1) := by sorry

end TokenQueue.ProductForm
