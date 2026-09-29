-- Prove2me | Theorems.Thm_RobustSDP_FullPert_well_posed
-- name    : RobustSDP.FullPert.well_posed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:58:59.845858+00:00
-- url     : https://prove2.me/theorems/07e6b204-fac9-4d51-aba1-ca684857958e
-- title:
--   §3.1 — $\|D\| < \rho^{-1}$ is necessary and sufficient for the LFR to be well defined on the ball $\|\Delta\| \le \rho$
-- statement:
--   Let $p, q$ be natural numbers, $D \in \mathbb{R}^{q\times p}$ and $\rho > 0$. Write $\|\cdot\|$ for the largest singular value. Then
--   $$\det(I - D\Delta) \neq 0 \ \text{ for every } \Delta \in \mathbb{R}^{p\times q} \text{ with } \|\Delta\| \le \rho \qquad\Longleftrightarrow\qquad \|D\| < \rho^{-1}.$$
--
--   Since the linear-fractional representation $\mathbf{F}(x,\Delta) = F(x) + L\Delta(I - D\Delta)^{-1}R(x) + (\cdot)^T$ involves $(I - D\Delta)^{-1}$ and its transpose, and nothing else that can fail to exist, this says that $\|D\| < \rho^{-1}$ is exactly the condition under which $\mathbf{F}(x,\Delta)$ is well defined for every $x \in \mathbb{R}^m$ and every $\Delta \in \mathbb{R}^{p\times q}$ with $\|\Delta\| \le \rho$. It is the standing assumption of the full-perturbation section and justifies it as no loss of generality.
--
--   **Formalization Note** "Well defined" is read as $\det(I - D\Delta) \neq 0$, which does not depend on $x$. The degenerate sizes $p = 0$ or $q = 0$ are allowed; both sides are then true.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 36, §3.1, first paragraph

import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.FullPert

/-- §3.1, p. 36 (first paragraph): for `ρ > 0`, `F(x, Δ)` is well defined, i.e.
`det (I − DΔ) ≠ 0`, for every `Δ ∈ ℝ^{p×q}` with `‖Δ‖ ≤ ρ` if and only if `‖D‖ < ρ⁻¹`
(spectral norms). -/
theorem well_posed {p q : ℕ} (D : Matrix (Fin q) (Fin p) ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ Δ : Matrix (Fin p) (Fin q) ℝ, ‖Δ‖ ≤ ρ → (1 - D * Δ).det ≠ 0) ↔ ‖D‖ < ρ⁻¹ := by sorry

end RobustSDP.FullPert
