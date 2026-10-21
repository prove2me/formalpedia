-- Prove2me | Theorems.Thm_SubsetShrink_DFO_eq_20_21
-- name    : SubsetShrink.DFO.eq_20_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:17.297288+00:00
-- url     : https://prove2.me/theorems/469fe634-3426-4520-9fb3-9e8654ebb0bf
-- title:
--   (20)–(21), p. 35, with (10), p. 9 — completing the square: minimizing Q_L(η, β) + λ‖η‖_q over ‖η‖₀ ≤ k is thresholding
-- statement:
--   Let $f:\mathbb R^p\to\mathbb R$, $\beta\in\mathbb R^p$, $L>0$, $\lambda\in\mathbb R$, $q\in\{1,2\}$ and $k\ge1$, and write $Q_L$ for the quadratic model (9) of $f$ and $\mathrm S$ for the thresholding operator (11).
--
--   1. For every $\eta\in\mathbb R^p$,
--   $$Q_L(\eta,\beta)+\lambda\|\eta\|_q=\frac L2\Big\|\eta-\Big(\beta-\frac1L\nabla f(\beta)\Big)\Big\|_2^2-\frac1{2L}\|\nabla f(\beta)\|_2^2+f(\beta)+\lambda\|\eta\|_q .$$
--   2. Consequently, for every $\hat\eta\in\mathbb R^p$,
--   $$\hat\eta\in\mathrm S\Big(\beta-\tfrac1L\nabla f(\beta);\,k;\,\tfrac\lambda L\ell_q\Big)\iff \|\hat\eta\|_0\le k\ \text{ and }\ Q_L(\hat\eta,\beta)+\lambda\|\hat\eta\|_q\le Q_L(\eta,\beta)+\lambda\|\eta\|_q\ \ \forall\,\eta:\ \|\eta\|_0\le k .$$
--
--   Part 1 is the step from the third to the fourth line of the proof of Proposition 2(a); part 2 is the equivalence (10) that makes the minimizer $\hat\eta$ of (20) a DFO step.
--
--   **Formalization Note** No smoothness of $f$ is needed: the identity is algebra on the vector $\nabla f(\beta)$. The infimum of (20) is not formed as a real number; the minimizer $\hat\eta$ is described by the minimality predicate.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 35, proof of Proposition 2 (A.1), (20)–(21); p. 9, (10)

import Mathlib
import Definitions.Def_SubsetShrink_DFO_Model

namespace SubsetShrink.DFO

/-- (20)–(21), p. 35, with the equivalence (10), p. 9 (Mazumder, Radchenko & Dedieu,
arXiv:1708.03288v4). For `L > 0`, `q ∈ {1, 2}`, `k ≥ 1`, any `f : ℝᵖ → ℝ` and `β ∈ ℝᵖ`:

1. completing the square, for every `η`,
   `Q_L(η, β) + λ‖η‖_q = (L/2)‖η − (β − (1/L)∇f(β))‖₂² − (1/(2L))‖∇f(β)‖₂² + f(β) + λ‖η‖_q`;
2. consequently `η̂ ∈ S(β − (1/L)∇f(β); k; (λ/L)ℓ_q)` if and only if `η̂` minimizes
   `η ↦ Q_L(η, β) + λ‖η‖_q` over `‖η‖₀ ≤ k`. -/
theorem eq_20_21 {p : ℕ} (f : E p → ℝ) (L lam : ℝ) (q k : ℕ)
    (hq : q = 1 ∨ q = 2) (hk : 1 ≤ k) (hLpos : 0 < L) (β : E p) :
    (∀ η : E p, QL f L η β + lam * lq q η =
        L / 2 * ‖η - (β - (1 / L) • gradient f β)‖ ^ 2 - 1 / (2 * L) * ‖gradient f β‖ ^ 2
          + f β + lam * lq q η) ∧
    (∀ ηhat : E p, IsThresh (β - (1 / L) • gradient f β) k (lam / L) q ηhat ↔
        (l0 ηhat ≤ k ∧ ∀ η : E p, l0 η ≤ k →
          QL f L ηhat β + lam * lq q ηhat ≤ QL f L η β + lam * lq q η)) := by sorry

end SubsetShrink.DFO
