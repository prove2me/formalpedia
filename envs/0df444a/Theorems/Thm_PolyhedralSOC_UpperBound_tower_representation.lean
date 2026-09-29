-- Prove2me | Theorems.Thm_PolyhedralSOC_UpperBound_tower_representation
-- name    : PolyhedralSOC.UpperBound.tower_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:47:02.77949+00:00
-- url     : https://prove2.me/theorems/5265e117-49b2-4dd8-b58d-96ce1fde32f1
-- title:
--   §2, Eq. (5) — the tower of 3-dimensional cones represents $\|y\|_2\le t$
-- statement:
--   Let $\theta\ge1$, $k=2^\theta$, $y\in\mathbb R^k$ and $t\in\mathbb R$. Then $(y,t)$ can be extended to a tower of variables $y_i^\ell$ (with $y_i^0=y_i$, $y_1^\theta=t$) solving
--   $$\sqrt{[y_{2i-1}^{\ell-1}]^2+[y_{2i}^{\ell-1}]^2}\le y_i^\ell,\qquad i=1,\dots,2^{\theta-\ell},\ \ell=1,\dots,\theta,\tag{5}$$
--   if and only if $(y,t)$ solves (CQI):
--   $$\sqrt{y_1^2+\dots+y_k^2}\le t.$$
--
--   The conic quadratic constraint of dimension $k+1$ is thereby represented exactly by $k-1$ conic quadratic constraints of dimension 3.
--
--   **Formalization Note** The norm is the Euclidean norm. The hypothesis $\theta\ge1$ excludes the degenerate case $k=1$, in which generation $0$ and generation $\theta$ would be the same variable.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), §2, p. 199, Eq. (5)

import Mathlib
import Definitions.Def_PolyhedralSOC_UpperBound_Tower

namespace PolyhedralSOC.UpperBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), §2, Eq. (5), p. 199 (PDF p. 7): for `k = 2^θ`,
`θ ≥ 1`, a pair `(y, t)` can be extended to a tower `Y` solving (5) if and only if
`(y, t)` solves (CQI) `√(y_1² + ⋯ + y_k²) ≤ t`. -/
theorem tower_representation (θ : ℕ) (hθ : 1 ≤ θ) (y : Fin (2 ^ θ) → ℝ) (t : ℝ) :
    (∃ Y : ℕ → ℕ → ℝ, IsTowerOf θ y t Y ∧ TowerSystem5 θ Y) ↔ Shared.eucNorm y ≤ t := by sorry

end PolyhedralSOC.UpperBound
