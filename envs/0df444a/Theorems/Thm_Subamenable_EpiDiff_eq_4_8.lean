-- Prove2me | Theorems.Thm_Subamenable_EpiDiff_eq_4_8
-- name    : Subamenable.EpiDiff.eq_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:40.080983+00:00
-- url     : https://prove2.me/theorems/7e6fec9d-74ad-4918-b35d-9b255bc40ac0
-- title:
--   Equation (4.8) — second subderivative of a convex PWLQ function
-- statement:
--   Let $\vartheta$ be convex piecewise linear-quadratic with pieces $\Omega_i$ and quadratic operators $A_i$. Fix $\bar y\in\operatorname{dom}\vartheta$ and $\bar u\in\partial\vartheta(\bar y)$. Then $\vartheta$ is properly twice epi-differentiable there. With $I(\bar y)=\{i:\bar y\in\Omega_i\}$ and $\bar u_i=\bar u-A_i\bar y-a_i$, its second subderivative has domain
--
--   $$\operatorname{dom}d^2\vartheta(\bar y,\bar u)=\bigcup_{i\in I(\bar y)}T_{\Omega_i}(\bar y)\cap\{\bar u_i\}^{\perp},$$
--
--   and equals $\langle A_iw,w\rangle$ on each corresponding piece; it is $+\infty$ outside the union. This is the outer-function calculation used in the composite formula.
--
--   **Formalization Note** A representation is passed explicitly because the piecewise formula names its pieces and coefficients. The result is quoted in the paper from the proof of Rockafellar–Wets Proposition 13.9.
-- source:
--   Mohammadi, Mordukhovich, Sarabi, Variational analysis of composite models with applications to continuous optimization, arXiv:1905.08837v2, p. 19, (4.8), extracted from proof of Rockafellar–Wets Proposition 13.9

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

open scoped InnerProductSpace

namespace Subamenable.EpiDiff

theorem eq_4_8 {m : ℕ} (theta : E m → EReal) (R : PWLQRep m)
    (ybar ubar : E m) (hrep : IsPWLQRep theta R)
    (hconv : IsConvexPWLQ theta) (hy : ybar ∈ dom theta)
    (hu : ubar ∈ NonconvexSplitting.Shared.LimitingSubdiff theta ybar) :
    IsProperlyTwiceEpiDiff theta ybar ubar ∧
    dom (secondSubderiv theta ybar ubar) =
      {w | ∃ i : Fin R.s, w ∈ pieceCritical R ybar ubar i} ∧
    (∀ i : Fin R.s, ∀ w ∈ pieceCritical R ybar ubar i,
      secondSubderiv theta ybar ubar w = ((⟪R.A i w, w⟫_ℝ : ℝ) : EReal)) ∧
    (∀ w, w ∉ {u | ∃ i : Fin R.s, u ∈ pieceCritical R ybar ubar i} →
      secondSubderiv theta ybar ubar w = ⊤) := by sorry

end Subamenable.EpiDiff
