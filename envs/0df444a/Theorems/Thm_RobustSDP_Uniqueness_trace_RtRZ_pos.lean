-- Prove2me | Theorems.Thm_RobustSDP_Uniqueness_trace_RtRZ_pos
-- name    : RobustSDP.Uniqueness.trace_RtRZ_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:07:31.273336+00:00
-- url     : https://prove2.me/theorems/946a97d1-8ba7-4d95-b5c5-412f02410552
-- title:
--   Appendix A — H3(b) excludes Tr LLᵀZ = Tr R(x)ᵀR(x)Z = 0 for Z ⪰ 0, Z ≠ 0; hence Tr R(x)ᵀR(x)Z > 0
-- statement:
--   Assume hypothesis H3(b): for every $x$, $\begin{bmatrix} L^T \\ R(x) \end{bmatrix}$ has full column rank. Let $Z \in \mathbb{R}^{n\times n}$ with $Z \succeq 0$ and $Z \neq 0$, let $x \in \mathbb{R}^m$ and $\tau \neq 0$. Then
--
--   1. the two equalities $\operatorname{Tr} LL^TZ = 0$ and $\operatorname{Tr} R(x)^TR(x)Z = 0$ do not both hold;
--   2. if moreover $\tau^2 \operatorname{Tr} LL^TZ = \operatorname{Tr} R(x)^TR(x)Z$, then
--   $$\operatorname{Tr} R(x)^T R(x) Z > 0 .$$
--
--   Applied at an optimal point with the dual matrix of Appendix A, this positivity is what makes the Hessian of the Lagrangian positive definite.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 49, Appendix A, paragraph starting 'From τ_opt ≠ 0'

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix

namespace RobustSDP.Uniqueness

/-- Appendix A, p. 49: by H3(b), `Tr LLᵀZ = 0` and `Tr R(x)ᵀR(x)Z = 0` cannot both hold for
`Z ⪰ 0`, `Z ≠ 0`; with `τ ≠ 0` and `τ² Tr LLᵀZ = Tr R(x)ᵀR(x)Z` this yields
`Tr R(x)ᵀR(x)Z > 0`. -/
theorem trace_RtRZ_pos {m n p q : ℕ} (D : SDPData m n p q) (h3b : D.H3b)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosSemidef) (hZ0 : Z ≠ 0)
    (x : Fin m → ℝ) (τ : ℝ) (hτ : τ ≠ 0) :
    ¬ ((D.L * D.Lᵀ * Z).trace = 0 ∧ ((D.R x)ᵀ * D.R x * Z).trace = 0) ∧
      (τ ^ 2 * (D.L * D.Lᵀ * Z).trace = ((D.R x)ᵀ * D.R x * Z).trace →
        0 < ((D.R x)ᵀ * D.R x * Z).trace) := by sorry

end RobustSDP.Uniqueness
