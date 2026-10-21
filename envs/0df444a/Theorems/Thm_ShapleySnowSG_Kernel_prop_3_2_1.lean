-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_prop_3_2_1
-- name    : ShapleySnowSG.Kernel.prop_3_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:51.239976+00:00
-- url     : https://prove2.me/theorems/cc1e28de-b5dc-4185-b9e3-58cc8e45d601
-- title:
--   Proposition 3.2.1, p. 14 — {v_λ} = T^Ṁ ⊂ S^Ṁ and {v_λ} ⊂ S^Ṙ ⊂ S^Δ̇ for the kernel-reduced array
-- statement:
--   Consider a discounted stochastic game with $n\ge1$ states, finite nonempty action sets, transition probabilities $q$ and discount factor $\lambda\in(0,1]$, with vector of values $v_\lambda$. For each state $k$ fix a Shapley–Snow kernel $\dot I_k\times\dot J_k$ of the local game $\mathcal G^k(\lambda,v_\lambda)$, and let $\dot D(\lambda)$ be the corresponding reduced array with auxiliary matrices $\dot\Delta^0,\dots,\dot\Delta^n$. Let $T^{\dot M},S^{\dot M},S^{\dot R},S^{\dot\Delta}\subset\mathbb R^n$ be the solution sets of
--   $$\mathrm{val}(\dot M^k_0+z^1\dot M^k_1+\dots+z^n\dot M^k_n)=0,\quad \det(\dot M^k_0+\dots+z^n\dot M^k_n)=0,$$
--   $$\mathrm{rank}(\dot\Delta^k-z^k\dot\Delta^0)<\max_{w\in\mathbb R}\mathrm{rank}(\dot\Delta^k-w\dot\Delta^0),\quad \det(\dot\Delta^k-z^k\dot\Delta^0)=0\qquad(1\le k\le n).$$
--   Then
--   $$\{v_\lambda\}=T^{\dot M}\subset S^{\dot M}\qquad\text{and}\qquad\{v_\lambda\}\subset S^{\dot R}\subset S^{\dot\Delta}.$$
--
--   This places the discounted values among the solutions of a finite algebraic system built from the kernels.
--
--   **Formalization Note** $v_\lambda$ is any $v$ satisfying the Shapley fixed-point relation (unique by `shapley_fixed_point`). Kernels are given by embeddings `r k : Fin (s k) ↪ I k`, `c k : Fin (s k) ↪ J k`. Action sets may depend on the state (§4, p. 20).
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 14, Proposition 3.2.1 (systems defined on p. 14)

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_StochasticGame

namespace ShapleySnowSG.Kernel

open Matrix

/-- Proposition 3.2.1, p. 14: for the reduced array `Ḋ(λ)` built from Shapley–Snow kernels of
the local games `G^k(λ, v_λ)`: `{v_λ} = T^Ṁ ⊂ S^Ṁ` and `{v_λ} ⊂ S^Ṙ ⊂ S^Δ̇`. -/
theorem prop_3_2_1 {n : ℕ} (hn : 0 < n) {I J : Fin n → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]
    [∀ k, Nonempty (I k)] [∀ k, Nonempty (J k)]
    (g : ∀ k, I k → J k → ℝ) (q : ∀ k, I k → J k → Fin n → ℝ)
    (hq0 : ∀ k i j l, 0 ≤ q k i j l) (hq1 : ∀ k i j, ∑ l, q k i j l = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (v : Fin n → ℝ) (hv : IsShapleyFixed g q lam v)
    (s : Fin n → ℕ) (r : ∀ k, Fin (s k) ↪ I k) (c : ∀ k, Fin (s k) ↪ J k)
    (hK : ∀ k, IsSSK (localGame g q lam v k) (s k) (r k) (c k)) :
    TM (redArray (dataArray g q lam) s r c) = {v} ∧
    TM (redArray (dataArray g q lam) s r c) ⊆ SM (redArray (dataArray g q lam) s r c) ∧
    v ∈ SR (redArray (dataArray g q lam) s r c) ∧
    SR (redArray (dataArray g q lam) s r c) ⊆ SDelta (redArray (dataArray g q lam) s r c) := by sorry

end ShapleySnowSG.Kernel
