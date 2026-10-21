-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_prop_2_4_4
-- name    : ShapleySnowSG.Kernel.prop_2_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:46.703218+00:00
-- url     : https://prove2.me/theorems/b744ff48-9e36-4a49-b816-83af2413af3c
-- title:
--   Proposition 2.4.4, p. 13 — Δ⁰ of one strict sign and positive left/right kernel vectors put z ∈ S^M into S^R
-- statement:
--   Let $D=(M^k_\ell)$ be an $n\times(n+1)$ array of real square matrices, the matrices of row $k$ having a common size, and suppose all the entries of $\Delta^0$ are nonzero and of the same sign. Let $z\in S^M$, and suppose that for each $1\le k\le n$ there are vectors $x^k,y^k$ with
--   $$x^k\in\mathrm{Ker}\,{}^t(M^k_0+z^1M^k_1+\dots+z^nM^k_n),\quad x^k>0,\qquad y^k\in\mathrm{Ker}(M^k_0+z^1M^k_1+\dots+z^nM^k_n),\quad y^k>0,$$
--   where $x>0$ means $x\ge0$ and $x\neq0$. Then $z\in S^R$, that is, $\mathrm{rank}(\Delta^k-z^k\Delta^0)<\max_{w\in\mathbb R}\mathrm{rank}(\Delta^k-w\Delta^0)$ for every $k$.
--
--   It shows that the discounted values survive the passage to the rank-drop system even when the pencils are singular.
--
--   **Formalization Note** The hypothesis on $\Delta^0$ is taken in the form of p. 13 (all entries positive or all negative); the appendix restatement on p. 30 asks that $(-1)^n\Delta^0$ be entrywise positive, a special case. $z$ is real.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 13, Proposition 2.4.4 (proved p. 31)

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_KroneckerMEP

namespace ShapleySnowSG.Kernel

open Matrix

/-- Proposition 2.4.4, p. 13: for an `n × (n+1)` array of square matrices whose `Δ^0` has all
entries nonzero and of the same sign, let `z ∈ S^M` and suppose that for each `k` there are
`x^k > 0` in `Ker ᵗ(M^k_0 + z^1 M^k_1 + ⋯ + z^n M^k_n)` and `y^k > 0` in
`Ker(M^k_0 + z^1 M^k_1 + ⋯ + z^n M^k_n)` (`> 0` meaning `≥ 0` and `≠ 0`). Then `z ∈ S^R`. -/
theorem prop_2_4_4 {n : ℕ} {p : Fin n → Type*} [∀ k, Fintype (p k)] [∀ k, DecidableEq (p k)]
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (p k) ℝ)
    (hΔ : (∀ i j, 0 < aux M 0 i j) ∨ (∀ i j, aux M 0 i j < 0))
    (z : Fin n → ℝ) (hz : z ∈ SM M) (x y : ∀ k, p k → ℝ)
    (hx : ∀ k, (pencil M z k)ᵀ *ᵥ x k = 0) (hxpos : ∀ k, 0 ≤ x k ∧ x k ≠ 0)
    (hy : ∀ k, pencil M z k *ᵥ y k = 0) (hypos : ∀ k, 0 ≤ y k ∧ y k ≠ 0) :
    z ∈ SR M := by sorry

end ShapleySnowSG.Kernel
