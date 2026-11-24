-- Prove2me | Theorems.Thm_RoughSurfaceScattering_laplace_h1_blowup
-- name    : RoughSurfaceScattering.laplace_h1_blowup
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T03:52:48.603055+00:00
-- url     : https://prove2.me/theorems/143f94fd-aec6-48dc-8aca-3805cb7a1328
-- title:
--   The Laplace fundamental solution $\Phi_0(\cdot,x_j)$ is unbounded in $H^1(D_0)$ as $x_j\to x_0$
-- statement:
--   Let $f\in BC^{1,1}(\mathbb R)$ describe the interface $\Gamma$, let $D^-=\{x:x_2<f(x_1)\}$, let $x_0=(s_0,f(s_0))\in\Gamma$ and let $n(x_0)$ be the unit normal of $\Gamma$ at $x_0$ pointing into $D^-$. Let $\delta>0$, put
--
--   $$x_j=x_0-\frac\delta j\,n(x_0)\qquad(j\ge1),$$
--
--   and let $D_0$ be any set with $B_{2\delta}(x_0)\cap D^-\subseteq D_0$. For every real constant $c\ne0$, with $\Phi_0(x,y)=\frac1{2\pi}\ln\frac1{|x-y|}$,
--
--   $$\sup_{j\ge1}\ \big\|c\,\Phi_0(\cdot,x_j)\big\|_{H^1(D_0)}=\infty .$$
--
--   The gradient of $\Phi_0(\cdot,x_j)$ has size $\frac1{2\pi|x-x_j|}$, which is not uniformly square integrable on a cone below $x_0$ as $x_j\to x_0$. Combined with Theorem 5.2, this shows that the transmitted field $u_-(\cdot,x_j)$ is unbounded in $H^1(D_0)$, which is the contradiction used in part (i) of the proof of Theorem 6.1.
--
--   **Formalization Note** The unboundedness is stated as: for every real $C$ some $j\ge1$ has $\|c\,\Phi_0(\cdot,x_j)\|_{H^1(D_0)}>C$, with the platform's `h1Norm`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, part (i), PDF p. 24 ("‖u_{1,-}^{(j)}‖_{H^1(D_0)} ≤ C ... which however contradicts with Theorem 5.2", i.e. the unboundedness of (2/(µ+1))Φ_0(·, x_j) in H^1(D_0)); Φ_0: Section 2, p. 4.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem laplace_h1_blowup (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (s0 δ : ℝ) (hδ : 0 < δ)
    (D0 : Set R2) (hD0 : Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0)
    (c : ℝ) (hc : c ≠ 0) :
    ∀ C : ℝ, ∃ j : ℕ, 1 ≤ j ∧ ENNReal.ofReal C <
      h1Norm D0 (fun x => (c : ℂ) * Phi 0 x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) := by sorry

end RoughSurfaceScattering
