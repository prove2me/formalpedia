-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_theorem_1
-- name    : TokenQueue.ProductForm.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:42.258306+00:00
-- url     : https://prove2.me/theorems/bc5ab25f-4803-41fb-9bdd-d3c62138be79
-- title:
--   Theorem 1, p. 7 — under Conditions 1–2 and stability, the stationary distribution of the token-based central queue is the product form (10)–(11)
-- statement:
--   Consider the token-based central queue with finitely many customer types and tokens, Poisson arrival rates $\lambda_c>0$, compatibility sets $\mathcal T_c\ne\emptyset$, a randomised assignment rule satisfying the **assignment condition** (Condition 1), and departure rates $\mu_{T_j}(x)=\eta(\phi(x))s_j(T_1,\dots,T_j)$ satisfying the **order-independent condition** (Condition 2), with $k(T_1,\dots,T_j)>0$ for non-empty sequences of distinct tokens. Suppose the queue is stable, i.e. the series in (11) converges. Then
--   $$\pi(x)=\pi((0))\,\frac{\Pi_\lambda(\{T_1,\dots,T_i\})}{\Pi_k(T_1,\dots,T_i)}\prod_{j=1}^{i}\alpha_j^{n_j}\prod_{j=1}^{\phi(x)}\frac1{\eta(j)},\qquad x=(T_1,n_1,\dots,T_i,n_i),\tag{10}$$
--   with $\Pi_\lambda(\{T_1,\dots,T_i\})=\prod_{j=1}^i\lambda_{T_j}(\{T_1,\dots,T_{j-1}\})$, $\Pi_k(T_1,\dots,T_i)=\prod_{j=1}^i k(T_1,\dots,T_j)$, $\alpha_j=\lambda_{\mathcal U(\{T_1,\dots,T_j\})}/k(T_1,\dots,T_j)$ and
--   $$\pi((0))=\Bigl(1+\sum_{x\ne(0)}\frac{\Pi_\lambda(\{T_1,\dots,T_i\})}{\Pi_k(T_1,\dots,T_i)}\prod_{j=1}^{i}\alpha_j^{n_j}\prod_{j=1}^{\phi(x)}\frac1{\eta(j)}\Bigr)^{-1},\tag{11}$$
--   is a stationary distribution of the queue: it is a probability distribution on the states, every state has total exit rate $\lambda+\mu(x)$, the mean exit rate $\sum_x\pi(x)(\lambda+\mu(x))$ is finite, and the global balance equations
--   $$\pi(x)\sum_y q(x,y)=\sum_y\pi(y)\,q(y,x)$$
--   hold for the transition rates $q$ of the queue (§4.1).
--
--   The sum over $x\ne(0)$ in (11) is the paper's sum over $i=1,\dots,K$, ordered $i$-tuples of distinct tokens and $(n_1,\dots,n_i)\in\mathbb N^i$. The theorem identifies the stationary distribution of a multi-type, multi-server central queue in closed product form, from which the paper derives the distributions of queue lengths, waiting and sojourn times.
--
--   **Formalization Note** "Stable" is read as summability of the weights (10), as in §4.4 (p. 9): when the series in (11) diverges, $\pi((0))=0$ and the queue is not ergodic. Uniqueness of the stationary distribution is **not** stated: the paper gets it from irreducibility and an ergodicity theorem of Foster [12], and the state type contains infeasible descriptors (weight $0$) outside the irreducible class. The added assumptions $\mathcal T_c\ne\emptyset$ and $k>0$ are explained in the definitions item. The global balance equations use the published predicate `KellyStochasticNetworks.FullBalance` (unconditional sums), and the conclusion includes the summability of the inflow at each state and of the exit-rate mass, so that no sum is a junk value. The rates $q$ are the **forward** transition rates of §4.1, not the right-hand side of (8).
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 7, Theorem 1, Eqs. (10)–(11); stability reading from §4.4, p. 9

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm

open Finset

/-- **Theorem 1**, p. 7. If the token-based central queue is stable (the series (11) converges) and
Conditions 1 and 2 hold, the normalised weights `π(x) = π((0)) Π_λ/Π_k ∏ α_j^{n_j} ∏ 1/η(j)` with
`π((0))` given by (11) form a probability distribution on the states that satisfies the global
balance equations of the queue's forward transition rates. -/
theorem theorem_1 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P) (hk : KPos P)
    (hstab : Summable (weight P)) :
    let π : State T → ℝ := fun x => weight P x / ∑' y, weight P y
    π State.empty = (1 + ∑' x : {x : State T // x.1 ≠ []}, weight P x.1)⁻¹ ∧
    (∀ x, π x = π State.empty * weight P x) ∧
    (∀ x, 0 ≤ π x) ∧ HasSum π 1 ∧
    (∀ x, HasSum (fun y => rate P x y) (lamTot P + mu P x.1)) ∧
    (∀ x, Summable (fun y => π y * rate P y x)) ∧
    Summable (fun x => π x * (lamTot P + mu P x.1)) ∧
    KellyStochasticNetworks.FullBalance π (rate P) := by sorry

end TokenQueue.ProductForm
