-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_dilation_det
-- name    : ShorNonsmooth.SpaceDilation.dilation_det
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:11:08.484408+00:00
-- url     : https://prove2.me/theorems/754acd34-d120-4be5-a75a-e573a7c56db7
-- title:
--   Determinant of the space-dilation operator is the coefficient
-- statement:
--   Let $\xi \in E_n$ be a unit vector and $\alpha$ a real coefficient. The space-dilation operator $R_\alpha(\xi)$, which stretches the $\xi$-component by $\alpha$ and fixes the orthogonal complement, has determinant $\alpha$. This is the one-step identity from which $\det A_k = (\prod_{j\le k}\alpha_j)\det A_0$ follows in the proof of Theorem 3.1.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 50, property of R_alpha(xi): dilation by alpha along xi, identity on the orthogonal complement; determinant step used in the proof of Theorem 3.1, p. 53.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- Shor (1985), p. 50: the determinant of the space-dilation operator `R_α(ξ)` along a unit vector `ξ` is `α` (eigenvalue `α` in direction `ξ`, eigenvalue `1` on the orthogonal complement). This is the one-step determinant identity behind `det A_k = (∏ α_j) det A_0` in the proof of Theorem 3.1 (p. 53). -/
theorem dilation_det {n : ℕ} (hn : 0 < n) (α : ℝ) (ξ : EuclideanSpace ℝ (Fin n))
    (hξ : ‖ξ‖ = 1) :
    LinearMap.det (dilation α ξ).toLinearMap = α := by sorry

end ShorNonsmooth.SpaceDilation
