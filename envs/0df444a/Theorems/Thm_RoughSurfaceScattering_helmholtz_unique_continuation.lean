-- Prove2me | Theorems.Thm_RoughSurfaceScattering_helmholtz_unique_continuation
-- name    : RoughSurfaceScattering.helmholtz_unique_continuation
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T05:29:44.670003+00:00
-- url     : https://prove2.me/theorems/50c425ec-f9b6-4c85-80f2-a130aa7d3fd4
-- title:
--   Unique continuation for the Helmholtz equation on a connected open set
-- statement:
--   Let $G\subseteq\mathbb R^2$ be a connected open set, $k\in\mathbb R$, and let $u_1,u_2\in C^2(G)$ solve
--
--   $$\Delta u_m+k^2u_m=0\quad\text{in }G\qquad(m=1,2).$$
--
--   If $u_1=u_2$ on a nonempty open subset $V\subseteq G$, then
--
--   $$u_1=u_2\quad\text{in }G .$$
--
--   Solutions of the Helmholtz equation are real analytic, and a real-analytic function on a connected open set that vanishes on a nonempty open subset vanishes identically. In the proof of Theorem 6.1 this carries the agreement of the scattered fields from the half plane above $\Gamma_c$ down to the whole region $D_1^+\cap D_2^+$ above both interfaces.
--
--   **Formalization Note** The Laplacian is Mathlib's `Laplacian.laplacian`; the functions are complex valued.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, PDF p. 22, first paragraph ("Following the same procedure in the proof of [49, Theorem 4.1] ..."); unique-continuation step (real analyticity of Helmholtz solutions, identity theorem on connected sets).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem helmholtz_unique_continuation (k : ℝ) (G : Set R2) (hG : IsOpen G)
    (hGc : IsConnected G) (u1 u2 : R2 → ℂ)
    (h1 : ContDiffOn ℝ 2 u1 G) (h2 : ContDiffOn ℝ 2 u2 G)
    (hH1 : IsHelmholtzOn G k u1) (hH2 : IsHelmholtzOn G k u2)
    (V : Set R2) (hV : IsOpen V) (hVne : V.Nonempty) (hVG : V ⊆ G)
    (heq : ∀ x ∈ V, u1 x = u2 x) :
    ∀ x ∈ G, u1 x = u2 x := by sorry

end RoughSurfaceScattering
