-- Prove2me | Theorems.Thm_TrustIPM_lemma_9
-- name    : TrustIPM.lemma_9
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:17:21.372076+00:00
-- url     : https://prove2.me/theorems/df21fa6b-975c-446e-a14f-883d8f5e5793
-- title:
--   Lemma 9 — $\|Ad_x\|_2\le(-d_x^THd_x-2\Delta(d_x))^{1/2}$ at a trust-region minimizer
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $g\in\mathbb R^n$, $H$ a symmetric $n\times n$ matrix, and $\Delta(u):=\tfrac12u^T(H+A^TA)u+g^Tu$. If $d_x\in\operatorname{argmin}_{u\in B_r(0)}\Delta(u)$ for some $r\ge0$, then
--
--   $$
--   \|Ad_x\|_2\le\sqrt{-d_x^THd_x-2\Delta(d_x)} .\tag{19}
--   $$
--
--   With $H=\nabla^2_{xx}\mathcal L(x,y)$ and $A=\sqrt\mu S^{-1}\nabla a(x)$ this bounds the scaled slack step $\|S^{-1}d_s\|_2$ by the predicted progress, display (21).
--
--   **Formalization Note** $A$ is a linear map between Euclidean spaces and $A^T$ its adjoint.
--
--   Differences from the source:
--   - encoding: symmetric matrix H ∈ ℝ^{m×n} → self-adjoint H : ℝⁿ → ℝⁿ; reason: H is added to AᵀA ∈ ℝ^{n×n} and is symmetric, so it is n×n; m×n is a typo
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, Lemma 9, p.13

import Mathlib
import Definitions.Def_TrustIPM_trsModel
open scoped InnerProductSpace RealInnerProductSpace

namespace TrustIPM

/-- **Lemma 9** (Hinder & Ye, *Worst-case iteration bounds for log barrier methods on problems with
nonconvex constraints*, arXiv:1807.00404v5, Lemma 9, p.13). Let `A ∈ ℝ^{m×n}`, `g ∈ ℝⁿ`, `H` a
symmetric `n × n` matrix, `Δ(u) := ½uᵀ(H + AᵀA)u + gᵀu`, and `d_x ∈ argmin_{u ∈ B_r(0)} Δ(u)` for some
`r ≥ 0`. Then `‖Ad_x‖₂ ≤ (−d_xᵀHd_x − 2Δ(d_x))^{1/2}` (19).

**Formalization Note** `ℝⁿ`, `ℝᵐ` are Euclidean spaces, `A` is a continuous linear map `ℝⁿ → ℝᵐ`
and `Aᵀ` its adjoint. The page's "`H ∈ ℝ^{m×n}`" is read as `n × n`, since `H` is symmetric and is
added to `AᵀA`. The square root is `Real.sqrt`. -/
theorem lemma_9 {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (g : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ u v, ⟪H u, v⟫_ℝ = ⟪u, H v⟫_ℝ) (r : ℝ) (hr : 0 ≤ r)
    (d : EuclideanSpace ℝ (Fin n)) (hd : d ∈ Metric.closedBall 0 r)
    (hmin : IsMinOn (trsModel (H + (ContinuousLinearMap.adjoint A).comp A) g)
      (Metric.closedBall 0 r) d) :
    ‖A d‖ ≤
      Real.sqrt (-⟪H d, d⟫_ℝ - 2 * trsModel (H + (ContinuousLinearMap.adjoint A).comp A) g d) := by sorry

end TrustIPM
