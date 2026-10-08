-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_remark_15
-- name    : SunNLSDP.Equiv.remark_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:39:06.905523+00:00
-- url     : https://prove2.me/theorems/3a7fc34f-0bf0-4f3b-9d79-acd95689a753
-- title:
--   Remark 15, p. 17 — z̄ strongly regular ⇔ Ξ̂ (equivalently Ξ) is a locally Lipschitz homeomorphism near z̄
-- statement:
--   Let $Z$ be a finite-dimensional real inner-product space, $\varphi:Z\to Z$ continuously differentiable, $D\subseteq Z$ nonempty closed convex, and $\bar z$ a solution of the generalized equation $0\in\varphi(z)+N_D(z)$ (53). Define
--
--   $$\widehat\Xi(z):=z-\Pi_D(z-\widehat\varphi(z)),\qquad \Xi(z):=z-\Pi_D(z-\varphi(z)),\qquad \widehat\varphi(z):=\varphi(\bar z)+J_z\varphi(\bar z)(z-\bar z).$$
--
--   Then $\bar z$ is a strongly regular solution of (53) if and only if $\widehat\Xi$ is a locally Lipschitz homeomorphism near $\bar z$, and if and only if $\Xi$ is.
--
--   A locally Lipschitz homeomorphism near $\bar z$ is a map whose restriction to some open neighbourhood $\mathcal V$ of $\bar z$ is a Lipschitz bijection onto its image with Lipschitz inverse.
--
--   **Formalization Note.** The paper states this as a consequence of Robinson [31, Lemma 3.1] and Kummer [18, Theorem 3.1]; nonemptiness of $D$ is added so that $\Pi_D$ is defined.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, p. 17, Remark 15, last sentence

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDP.Equiv
theorem remark_15 {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
    (φ : Z → Z) (hφ : ContDiff ℝ 1 φ)
    (D : Set Z) (hD : IsClosed D) (hDc : Convex ℝ D) (hDne : D.Nonempty)
    (zbar : Z) (hsol : -φ zbar ∈ RobinsonSR.Reduction.normalCone D zbar) :
    (StronglyRegular φ D zbar ↔
      LocLipHomeo (fun z => z - metricProj D (z - (φ zbar + fderiv ℝ φ zbar (z - zbar)))) zbar) ∧
    (StronglyRegular φ D zbar ↔ LocLipHomeo (fun z => z - metricProj D (z - φ z)) zbar) := by sorry
end SunNLSDP.Equiv
