-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_shapley_fixed_point
-- name    : ShapleySnowSG.Kernel.shapley_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:35.82247+00:00
-- url     : https://prove2.me/theorems/6384c849-a4dc-4a04-b922-36eeb800f7fd
-- title:
--   §2.1, p. 7, result 2 — v_λ is the unique fixed point of the Shapley operator, a (1 − λ)-contraction in L∞
-- statement:
--   Consider a discounted stochastic game with $n\ge1$ states, finite nonempty action sets $I_k,J_k$, payoff $g$, transition probabilities $q(\cdot\mid k,i,j)$ and discount factor $\lambda\in(0,1]$, and its local games $\mathcal G^k(\lambda,z)$.
--
--   1. Every local game $\mathcal G^k(\lambda,z)$ has a unique value, so the Shapley operator $\Phi^k(\lambda,z)=\mathrm{val}(\mathcal G^k(\lambda,z))$ is well defined.
--   2. $\Phi(\lambda,\cdot)$ has a unique fixed point $v_\lambda\in\mathbb R^n$.
--   3. $\Phi(\lambda,\cdot)$ is a contraction of modulus $1-\lambda$ for the $L^\infty$ norm:
--   $$\max_k\big|\Phi^k(\lambda,z)-\Phi^k(\lambda,\bar z)\big|\le(1-\lambda)\max_k|z^k-\bar z^k|\qquad\text{for all }z,\bar z\in\mathbb R^n.$$
--
--   This is Shapley's 1953 theorem as recalled in the paper; it supplies the vector $v_\lambda$ about which the main theorem speaks.
--
--   **Formalization Note** Since the value is a relation, part 3 is stated for any vectors $w,\bar w$ of values of the local games at $z,\bar z$. The norm on $\mathbb R^n$ is Mathlib's sup norm on `Fin n → ℝ`, i.e. the $L^\infty$ norm.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 7, §2.1, result 2

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_StochasticGame

namespace ShapleySnowSG.Kernel

open Matrix

/-- §2.1, p. 7, result 2 (Shapley): for `λ ∈ (0, 1]` every local game has a value, the Shapley
operator has a unique fixed point `v_λ`, and it is a `(1 − λ)`-contraction for the `L^∞` norm. -/
theorem shapley_fixed_point {n : ℕ} (hn : 0 < n) {I J : Fin n → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]
    [∀ k, Nonempty (I k)] [∀ k, Nonempty (J k)]
    (g : ∀ k, I k → J k → ℝ) (q : ∀ k, I k → J k → Fin n → ℝ)
    (hq0 : ∀ k i j l, 0 ≤ q k i j l) (hq1 : ∀ k i j, ∑ l, q k i j l = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (∀ (z : Fin n → ℝ) (k : Fin n), ∃! w : ℝ, IsMatVal (localGame g q lam z k) w) ∧
    (∃! v : Fin n → ℝ, IsShapleyFixed g q lam v) ∧
    (∀ z zb w wb : Fin n → ℝ, (∀ k, IsMatVal (localGame g q lam z k) (w k)) →
      (∀ k, IsMatVal (localGame g q lam zb k) (wb k)) → ‖w - wb‖ ≤ (1 - lam) * ‖z - zb‖) := by sorry

end ShapleySnowSG.Kernel
