-- Prove2me | Theorems.Thm_SubSuperStoch_AsyncTrack_error_system
-- name    : SubSuperStoch.AsyncTrack.error_system
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:06.743418+00:00
-- url     : https://prove2.me/theorems/6a5c6894-0acd-4ae6-8f59-5838f3474e7f
-- title:
--   (3.6), p. 15 — under C1 the errors (3.5) obey e_x(k+1) = (M(k) ⊗ I_p) e_x(k)
-- statement:
--   Consider the asynchronous leader–follower network (3.1)–(3.3) with step size $\tau$, gain $\psi$ and arbitrary communication instants. Assume condition C1: the signed digraph is structurally balanced with respect to the partition $\mathcal V_1=\{v_0\}\cup V_1$, $\mathcal V_2=\{v_1,\dots,v_n\}\setminus V_1$. Define the error coordinates (3.5)
--   $$e_i(k)=x_i(k)-x_0(k)\ \ (v_i\in V_1),\qquad e_i(k)=-x_i(k)-x_0(k)\ \ (v_i\notin V_1).$$
--   Then along every trajectory, for all $k\in\mathbb N$ and every follower $i$,
--   $$e_i(k+1)=\sum_{j=1}^n[M(k)]_{ij}\,e_j(k),$$
--   which is the error system $e_x(k+1)=[M(k)\otimes I_p]\,e_x(k)$ written coordinate-wise.
--
--   The identity converts bipartite tracking (followers in $\mathcal V_1$ approach $x_0$, followers in $\mathcal V_2$ approach $-x_0$) into the convergence to zero of the products $M(k)\cdots M(0)$.
--
--   **Formalization Note** The stacked vector $e_x(k)\in\mathbb R^{np}$ and the Kronecker product are replaced by the equivalent coordinate-wise identity on the blocks $e_i(k)\in\mathbb R^p$. The gain bound (3.7), $\tau>0$, $\psi>0$ and the asynchronous-instant condition (2.10) are not assumed: the identity is algebraic and holds without them.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 15, (3.4), (3.5) and (3.6)

import Mathlib
import Definitions.Def_SubSuperStoch_AsyncTrack_SignedDigraph
import Definitions.Def_SubSuperStoch_AsyncTrack_AsyncModel

namespace SubSuperStoch.AsyncTrack

/-- (3.5)–(3.6), p. 15: under condition C1 (with partition `𝒱₁ = {v₀} ∪ V₁`), every trajectory of
(3.1)–(3.3) satisfies the error system `e_x(k+1) = (M(k) ⊗ I_p) e_x(k)`, written coordinate-wise:
`e_i(k+1) = ∑_j [M(k)]_{ij} e_j(k)`. -/
theorem error_system {n p : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (τ ψ : ℝ) (s : Fin n → ℕ → ℕ)
    (V₁ : Set (Fin n)) (hC1 : StructBalanced a b V₁)
    (x0 : ℕ → EuclideanSpace ℝ (Fin p)) (x : Fin n → ℕ → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun a b τ ψ s x0 x) :
    ∀ k i, errVec V₁ x0 x i (k + 1) = ∑ j, Mmat a b τ ψ s k i j • errVec V₁ x0 x j k := by sorry

end SubSuperStoch.AsyncTrack
