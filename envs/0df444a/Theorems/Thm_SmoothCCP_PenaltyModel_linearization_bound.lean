-- Prove2me | Theorems.Thm_SmoothCCP_PenaltyModel_linearization_bound
-- name    : SmoothCCP.PenaltyModel.linearization_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:24.441236+00:00
-- url     : https://prove2.me/theorems/958f2e44-3687-4073-ae20-e012bb843726
-- title:
--   Proof of Proposition 5.3, (5.7)–(5.8), p. 18 — ‖C^N(x+d) − C̃^N(x;d)‖ ≤ √N L′‖d‖²
-- statement:
--   Let $c_1,\dots,c_m:\mathbb R^n\times\Xi\to\mathbb R$ ($m\ge1$) and fix a sample $\xi_1,\dots,\xi_N$. Suppose that every $c_j(\cdot,\xi_i)$ is differentiable on $\mathbb R^n$ and that its gradient is Lipschitz continuous with a constant $L'>0$:
--   $$
--   \|\nabla c_j(x,\xi_i)-\nabla c_j(y,\xi_i)\|\le L'\|x-y\|\qquad\text{for all }x,y\in\mathbb R^n,\ i,\ j .
--   $$
--   Write $C_y=C^N(y)$ for the vector with entries $\max_j c_j(y,\xi_i)$ and $\widetilde C_{(x;d)}=\widetilde C^N(x;d)$ for the vector with entries $\max_j\{c_j(x,\xi_i)+\nabla c_j(x,\xi_i)^{\mathsf T}d\}$. Then for all $x,d\in\mathbb R^n$
--   $$
--   \big\|C_{x+d}-\widetilde C_{(x;d)}\big\|_2\le\sqrt N\,L'\,\|d\|^2 .
--   $$
--
--   This is the step of the proof of Proposition 5.3 showing that replacing each maximum of the $c_j$ by the maximum of their linearizations costs only $O(\|d\|^2)$.
--
--   **Formalization Note** The norm on $\mathbb R^N$ is the Euclidean one, written out as $\sqrt{\sum_i(\cdot)^2}$, which is what the factor $\sqrt N$ refers to. The Lipschitz hypothesis is taken on all of $\mathbb R^n$ (the paper writes $x,y\in X$; see Proposition 5.3) and per component $j$.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, proof of Proposition 5.3, (5.7), (5.8) and the sentence after them, p. 18

import Mathlib
import Definitions.Def_SmoothCCP_PenaltyModel_Setting

namespace SmoothCCP.PenaltyModel

/-- Proof of Proposition 5.3, (5.7)–(5.8), arXiv:1905.07377v2, p. 18: if each cⱼ(·, ξᵢ) is
differentiable with L′-Lipschitz gradient on ℝⁿ, then
‖C^N(x + d) − C̃^N(x; d)‖ ≤ √N L′‖d‖² (Euclidean norm on ℝᴺ) for all x, d ∈ ℝⁿ. -/
theorem linearization_bound {n m N : ℕ} {Ξ : Type} (hm : 1 ≤ m) (ξs : Fin N → Ξ)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (L' : ℝ) (hL' : 0 < L')
    (hc : ∀ i j, Differentiable ℝ (fun x => c j x (ξs i)))
    (h55 : ∀ (x y : EuclideanSpace ℝ (Fin n)) (i : Fin N) (j : Fin m),
      ‖gradient (fun z => c j z (ξs i)) x - gradient (fun z => c j z (ξs i)) y‖ ≤ L' * ‖x - y‖)
    (x d : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt (∑ i, (CN hm c ξs (x + d) i - Ctil hm c ξs x d i) ^ 2)
      ≤ Real.sqrt N * L' * ‖d‖ ^ 2 := by sorry

end SmoothCCP.PenaltyModel
