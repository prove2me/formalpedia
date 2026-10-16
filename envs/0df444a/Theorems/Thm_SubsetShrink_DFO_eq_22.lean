-- Prove2me | Theorems.Thm_SubsetShrink_DFO_eq_22
-- name    : SubsetShrink.DFO.eq_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:23.527314+00:00
-- url     : https://prove2.me/theorems/dd1d3a32-2ef9-4dd3-a259-206ee1360f2e
-- title:
--   (22), p. 35 — one DFO step decreases F by at least (L − L₀)/2 ‖η̂ − β‖²
-- statement:
--   Let $f:\mathbb R^p\to\mathbb R$ be differentiable and convex with $L_0$-Lipschitz gradient, $L_0\ge0$, and let $L\ge L_0$ with $L>0$, $\lambda\in\mathbb R$, $q\in\{1,2\}$, $k\ge1$. Put $F(\beta)=f(\beta)+\lambda\|\beta\|_q$. If $\|\beta\|_0\le k$ and
--   $$\hat\eta\in\mathrm S\Big(\beta-\tfrac1L\nabla f(\beta);\,k;\,\tfrac\lambda L\ell_q\Big),$$
--   then
--   $$F(\beta)\ge\frac{L-L_0}2\|\hat\eta-\beta\|_2^2+F(\hat\eta).$$
--
--   Applied with $\beta=\beta^{(m)}$ and $\hat\eta=\beta^{(m+1)}$, this is the sufficient-decrease inequality of the DFO method, from which both parts of Proposition 2 follow.
--
--   **Formalization Note** No sign condition on $\lambda$ or $f$ is needed here. $L>0$ is required for the step $1/L$ to be the paper's.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 35, proof of Proposition 2 (A.1), (22)

import Mathlib
import Definitions.Def_SubsetShrink_DFO_Model

namespace SubsetShrink.DFO

/-- (22), p. 35 (Mazumder, Radchenko & Dedieu, arXiv:1708.03288v4). Let `f : ℝᵖ → ℝ` be
differentiable and convex with `L₀`-Lipschitz gradient ((8)), `L ≥ L₀` with `L > 0`,
`q ∈ {1, 2}`, `k ≥ 1`. If `‖β‖₀ ≤ k` and `η̂ ∈ S(β − (1/L)∇f(β); k; (λ/L)ℓ_q)`, then
`F(β) ≥ ((L − L₀)/2)‖η̂ − β‖₂² + F(η̂)`, where `F(β) = f(β) + λ‖β‖_q`. -/
theorem eq_22 {p : ℕ} (f : E p → ℝ) (L0 L lam : ℝ) (q k : ℕ)
    (hq : q = 1 ∨ q = 2) (hk : 1 ≤ k)
    (hdiff : Differentiable ℝ f) (hconv : ConvexOn ℝ Set.univ f) (hL0nn : 0 ≤ L0)
    (hL0 : ∀ β α : E p, ‖gradient f β - gradient f α‖ ≤ L0 * ‖β - α‖)
    (hL : L0 ≤ L) (hLpos : 0 < L)
    (β ηhat : E p) (hβ : l0 β ≤ k)
    (hη : IsThresh (β - (1 / L) • gradient f β) k (lam / L) q ηhat) :
    (L - L0) / 2 * ‖ηhat - β‖ ^ 2 + F f lam q ηhat ≤ F f lam q β := by sorry

end SubsetShrink.DFO
