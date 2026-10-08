-- Prove2me | Theorems.Thm_RWPI_Limit_proposition_3
-- name    : RWPI.Limit.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:10:07.488205+00:00
-- url     : https://prove2.me/theorems/861aad61-a047-4ce8-af95-0085f365d039
-- title:
--   Proposition 3 — strong duality: $R_n(\theta) = \sup_\lambda\{-\frac1n\sum_i \sup_u\{\lambda^T h(u,\theta) - c(u, W_i)\}\}$
-- statement:
--   Let $W_1, \dots, W_n \in \mathbb R^m$ ($n \ge 1$) be distinct sample points with empirical distribution $\mathbb P_n$. Let $c : \mathbb R^m \times \mathbb R^m \to [0, \infty)$ be a lower semicontinuous cost with $c(u, u) = 0$ for all $u$. Let $h : \mathbb R^m \times \mathbb R^l \to \mathbb R^r$ and $\theta \in \mathbb R^l$ be such that $h(\cdot, \theta)$ is Borel measurable and $\mathbf 0$ lies in the interior of the convex hull of $\{h(u, \theta) : u \in \mathbb R^m\}$. Then the RWP function $R_n(\theta) = \inf\{D_c(P, \mathbb P_n) : \mathbb E_P[h(W, \theta)] = \mathbf 0\}$ satisfies
--
--   $$
--   R_n(\theta) = \sup_{\lambda \in \mathbb R^r} \Big\{ -\frac1n \sum_{i=1}^n \sup_{u \in \mathbb R^m} \big\{ \lambda^T h(u, \theta) - c(u, W_i) \big\} \Big\} .
--   $$
--
--   This is strong duality for the problem of moments that defines $R_n$: it turns an infimum over probability measures into a finite-dimensional supremum over the multiplier $\lambda$, and it is the starting point of the asymptotic analysis of the RWP function (Eq. (31) and Theorem 3).
--
--   **Formalization Note.** Both sides are compared in the extended reals: an inner supremum may be $+\infty$, which makes the corresponding term $-\infty$. The paper states the result for a $[0,\infty]$-valued cost with $\Omega = \{c < \infty\}$ Borel and non-empty; here the cost is finite everywhere, so $\Omega = \mathbb R^m \times \mathbb R^m$. This is the setting of §3 (the cost (17)), and it is needed: for a cost that is infinite on part of the space, the interior condition on $\{h(u,\theta) : u \in \mathbb R^m\}$ does not imply the Slater condition that the proof in App. B uses.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 13, Proposition 3 (proof App. B, pp. 46–47)

import Mathlib
import Definitions.Def_RWPI_Limit_rwp
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution

open MeasureTheory

namespace RWPI.Limit

/-- Proposition 3 (Blanchet, Kang & Murthy, arXiv:1610.05627v4, p. 13; proof App. B, pp. 46–47):
strong duality for the RWP function. For distinct sample points `w_1, …, w_n` (§3.1 standing
assumption), a lower semicontinuous cost `c` with `c(u, u) = 0` (§2.1) that is finite everywhere
(so `Ω = {c < ∞} = ℝ^m × ℝ^m`, Borel and non-empty), a Borel measurable `h(·, θ)` and
`0 ∈ int conv {h(u, θ) : u ∈ ℝ^m}`,
`R_n(θ) = sup_λ { −(1/n) Σ_i sup_u { λ^T h(u, θ) − c(u, W_i) } }`, in `EReal`. -/
theorem proposition_3 {m l r n : ℕ} (hn : 0 < n) (w : Fin n → (Fin m → ℝ))
    (hw : Function.Injective w)
    (c : (Fin m → ℝ) → (Fin m → ℝ) → ENNReal)
    (hc_lsc : LowerSemicontinuous (Function.uncurry c))
    (hc_diag : ∀ u, c u u = 0) (hc_fin : ∀ u v, c u v ≠ ⊤)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θ : Fin l → ℝ)
    (hmeas : Measurable fun u => h u θ)
    (hint : (0 : Fin r → ℝ) ∈ interior (convexHull ℝ (Set.range fun u => h u θ))) :
    (rwp c h θ (WassersteinDRO.Regularization.empiricalDistribution w) : EReal) =
      ⨆ lam : Fin r → ℝ, -(((1 / (n : ℝ) : ℝ) : EReal) *
        ∑ i, ⨆ u : Fin m → ℝ, (((lam ⬝ᵥ h u θ : ℝ) : EReal) - (c u (w i) : EReal))) := by sorry

end RWPI.Limit
