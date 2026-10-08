-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_lemma_2
-- name    : SunNLSDP.Equiv.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:43.689849+00:00
-- url     : https://prove2.me/theorems/6f8a4bb9-f8c4-4b2d-82a8-be02cba067b3
-- title:
--   Lemma 2, pp. 6–7 — every V ∈ ∂Π_D(y) is self-adjoint, positive semidefinite and satisfies ⟨Vd, d − Vd⟩ ≥ 0
-- statement:
--   Let $Z$ be a finite-dimensional real inner-product space, $D\subseteq Z$ a nonempty closed convex set and $\Pi_D$ the metric projector onto $D$. For every $y\in Z$ and every $V$ in Clarke's generalized Jacobian $\partial\Pi_D(y)$:
--
--   1. $V$ is self-adjoint;
--   2. $\langle d,Vd\rangle\ge0$ for all $d\in Z$;
--   3. $\langle Vd,\,d-Vd\rangle\ge0$ for all $d\in Z$.
--
--   These three properties of generalized Jacobians of projectors are used in the proof of Proposition 7 (on $\mathcal S^{|\beta|}_+$).
--
--   **Formalization Note.** Nonemptiness of $D$ is added: the paper's $\Pi_D$ is only defined for nonempty $D$.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, pp. 6–7, Lemma 2 (citing Meng, Sun and Zhao [21, Proposition 1])

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDP.Equiv
theorem lemma_2 {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
    (D : Set Z) (hD : IsClosed D) (hDc : Convex ℝ D) (hDne : D.Nonempty)
    (y : Z) (V : Z →L[ℝ] Z) (hV : V ∈ clarkeJac (metricProj D) y) :
    (∀ u w : Z, ⟪V u, w⟫ = ⟪u, V w⟫) ∧
    (∀ d : Z, 0 ≤ ⟪d, V d⟫) ∧
    (∀ d : Z, 0 ≤ ⟪V d, d - V d⟫) := by sorry
end SunNLSDP.Equiv
