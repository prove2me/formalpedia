-- Prove2me | Theorems.Thm_RoughSurfaceScattering_helmholtz_line_identity
-- name    : RoughSurfaceScattering.helmholtz_line_identity
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T05:29:32.831145+00:00
-- url     : https://prove2.me/theorems/e53e8f2c-b119-49f8-997b-1f594f8671fe
-- title:
--   Helmholtz solutions agreeing on a segment of a line agree on the whole line
-- statement:
--   Let $G\subseteq\mathbb R^2$ be open and $k\in\mathbb R$, and let $u_1,u_2\in C^2(G)$ solve the Helmholtz equation
--
--   $$\Delta u_m+k^2u_m=0\quad\text{in }G\qquad(m=1,2).$$
--
--   Suppose $G$ contains the whole line $\Gamma_c=\{(t,c):t\in\mathbb R\}$. If $u_1=u_2$ on the segment $\Gamma_{c,d}=\{(t,c):|t|\le d\}$ for some $d>0$, then
--
--   $$u_1=u_2\quad\text{on }\Gamma_c .$$
--
--   Classical solutions of the Helmholtz equation are real analytic, so $t\mapsto(u_1-u_2)(t,c)$ is a real-analytic function on $\mathbb R$ that vanishes on an interval. By the identity theorem it vanishes identically. This is the first step of the continuation argument of [49, Theorem 4.1] used in the proof of Theorem 6.1.
--
--   **Formalization Note** The Laplacian is Mathlib's `Laplacian.laplacian`, which for $C^2$ functions on an open set is the classical one.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, PDF p. 22, first paragraph ("Following the same procedure in the proof of [49, Theorem 4.1] ..."); analyticity step: solutions of the Helmholtz equation are real analytic, so equality on Γ_{c,d} extends to the line Γ_c.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem helmholtz_line_identity (k : ℝ) (G : Set R2) (hG : IsOpen G) (u1 u2 : R2 → ℂ)
    (h1 : ContDiffOn ℝ 2 u1 G) (h2 : ContDiffOn ℝ 2 u2 G)
    (hH1 : IsHelmholtzOn G k u1) (hH2 : IsHelmholtzOn G k u2)
    (c d : ℝ) (hd : 0 < d) (hline : ∀ t : ℝ, pt t c ∈ G)
    (hseg : ∀ x ∈ measSeg c d, u1 x = u2 x) :
    ∀ t : ℝ, u1 (pt t c) = u2 (pt t c) := by sorry

end RoughSurfaceScattering
