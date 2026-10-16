-- Prove2me | Theorems.Thm_SubsetShrink_LowerBound_eq_40
-- name    : SubsetShrink.LowerBound.eq_40
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:49.064366+00:00
-- url     : https://prove2.me/theorems/12a19972-b5cd-4599-b9be-026372d19955
-- title:
--   (40), p. 45 — for v ∈ 𝒱_k, H(c_v v) = −c_v² and min_{‖β‖₀≤k} G(β) ≤ −c_v²
-- statement:
--   Let $X$ be a real $n\times p$ matrix, $k$ a nonnegative integer, $\beta^*,\tilde\beta^*\in\mathbb R^p$ and $\epsilon\in\mathbb R^n$, with $\|\tilde\beta^*\|_0\le k/2$. With $y$, $\Delta^*$, $\tilde S$, $G$ and $H$ as in (39), let
--   $$
--   \mathcal V_k=\{v\in\mathbb R^p:\ \operatorname{supp}(v)\subseteq\tilde S^c,\ \|v\|_0\le k/2,\ \|Xv\|=1\},\qquad c_v=(\Delta^*+\epsilon)^\top Xv .
--   $$
--   Then for every $v\in\mathcal V_k$,
--   $$
--   H(c_v v)=-c_v^2,
--   $$
--   and there is $\beta\in\mathbb R^p$ with $\|\beta\|_0\le k$ and
--   $$
--   G(\beta)\le-\big|(\Delta^*+\epsilon)^\top Xv\big|^2 .
--   $$
--
--   Taken over all $v\in\mathcal V_k$, this is (40): $\min_{\|\beta\|_0\le k}G(\beta)\le-\max_{\mathcal V_k}|(\Delta^*+\epsilon)^\top Xv|^2$. It turns a large correlation of the noise with some sparse direction into a large decrease of the best-subsets objective below its value at $\tilde\beta^*$.
--
--   **Formalization Note** The minimum and maximum of (40) are stated pointwise in $v$: for each $v\in\mathcal V_k$ a feasible $\beta$ is exhibited by an existential. This is equivalent to (40) and has no junk value when $\mathcal V_k$ is empty. $\|\cdot\|_0\le k/2$ is a real comparison.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 45, proof of Theorem 4 (B.9), the definition of 𝒱_k and c_v, the display after it, and (40)

import Mathlib
import Definitions.Def_SubsetShrink_LowerBound_Model

namespace SubsetShrink.LowerBound

/-- Proof of Theorem 4, (40), p. 45, in pointwise form: for every `v ∈ 𝒱_k` (support in `S̃ᶜ`,
`‖v‖₀ ≤ k/2`, `‖Xv‖ = 1`), with `c_v = (Δ* + ε)⊤Xv`, one has `H(c_v v) = −c_v²`, and some `β` with
`‖β‖₀ ≤ k` has `G(β) ≤ −c_v²`. Here `y = Xβ* + ε`, `Δ* = Xβ* − Xβ̃*`, `S̃ = supp β̃*`, `‖β̃*‖₀ ≤ k/2`. -/
theorem eq_40 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (βstar βt : Fin p → ℝ) (ε : Fin n → ℝ) (hβt : (l0 βt : ℝ) ≤ (k : ℝ) / 2)
    (v : Fin p → ℝ) (hv : supp v ⊆ (supp βt)ᶜ) (hv0 : (l0 v : ℝ) ≤ (k : ℝ) / 2)
    (hXv : SubsetShrink.Events.l2 (X.mulVec v) = 1) :
    Hfun X (X.mulVec βstar - X.mulVec βt + ε)
        (SubsetShrink.Events.dot (X.mulVec βstar - X.mulVec βt + ε) (X.mulVec v) • v) =
      -(SubsetShrink.Events.dot (X.mulVec βstar - X.mulVec βt + ε) (X.mulVec v)) ^ 2 ∧
    ∃ β : Fin p → ℝ, l0 β ≤ k ∧
      Gfun X (X.mulVec βstar + ε) βt β ≤
        -(SubsetShrink.Events.dot (X.mulVec βstar - X.mulVec βt + ε) (X.mulVec v)) ^ 2 := by sorry

end SubsetShrink.LowerBound
