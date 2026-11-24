-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_l2_blowup
-- name    : RoughSurfaceScattering.dipole_l2_blowup
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T03:43:57.997929+00:00
-- url     : https://prove2.me/theorems/deea2383-3612-4153-81b6-830e122db20e
-- title:
--   The Laplace dipole $\nabla_x\Phi_0(\cdot,x_j)\cdot n(x_0)$ is unbounded in $L^2(D_0)$ as $x_j\to x_0$
-- statement:
--   Let $f\in BC^{1,1}(\mathbb R)$ describe the interface $\Gamma$, let $D^-=\{x:x_2<f(x_1)\}$, let $x_0=(s_0,f(s_0))\in\Gamma$ and let $n(x_0)$ be the unit normal of $\Gamma$ at $x_0$ pointing into $D^-$. Let $\delta>0$, put
--
--   $$x_j=x_0-\frac\delta j\,n(x_0)\qquad(j\ge1),$$
--
--   and let $D_0\subseteq\mathbb R^2$ be any set with $B_{2\delta}(x_0)\cap D^-\subseteq D_0$. With $\Phi_0(x,y)=\frac1{2\pi}\ln\frac1{|x-y|}$,
--
--   $$\sup_{j\ge1}\ \big\|\nabla_x\Phi_0(\cdot,x_j)\cdot n(x_0)\big\|_{L^2(D_0)}=\infty .$$
--
--   As the source points $x_j$ approach $x_0$ from above, the dipole field behaves like $|x-x_j|^{-1}$ on a cone below $x_0$, and its $L^2$ norm grows like $\sqrt{\ln j}$. This is the blow-up the paper uses for the contradiction in parts (ii) and (iii) of the proof of Theorem 6.1.
--
--   **Formalization Note** The unboundedness is stated as: for every real $C$ some $j\ge1$ has $\|\cdot\|_{L^2(D_0)}>C$. $L^2(D_0)$ is taken for Lebesgue measure restricted to $D_0$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, parts (ii)–(iii), PDF p. 25 (the bound ‖∇_x Φ_0(x, x_j)·n(x_0)‖_{L^2(D_0)} ≤ C is "a contradiction"); Φ_0: Section 2, p. 4.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_l2_blowup (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (s0 δ : ℝ) (hδ : 0 < δ)
    (D0 : Set R2) (hD0 : Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0) :
    ∀ C : ℝ, ∃ j : ℕ, 1 ≤ j ∧ ENNReal.ofReal C <
      l2Norm D0 (dipoleSource 0 (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0)) := by sorry

end RoughSurfaceScattering
