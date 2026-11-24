-- Prove2me | Theorems.Thm_RoughSurfaceScattering_helmholtz_h1_blowup
-- name    : RoughSurfaceScattering.helmholtz_h1_blowup
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T04:01:13.154659+00:00
-- url     : https://prove2.me/theorems/923b6f9f-2a04-4243-b936-93313adc8d0a
-- title:
--   The Helmholtz fundamental solution $\Phi_k(\cdot,x_j)$ is unbounded in $H^1(D_0)$ as $x_j\to x_0$
-- statement:
--   Let $f\in BC^{1,1}(\mathbb R)$ describe the interface $\Gamma$, let $D^-=\{x:x_2<f(x_1)\}$, let $x_0=(s_0,f(s_0))\in\Gamma$ and let $n(x_0)$ be the unit normal of $\Gamma$ at $x_0$ pointing into $D^-$. Let $\delta>0$, put
--
--   $$x_j=x_0-\frac\delta j\,n(x_0)\qquad(j\ge1),$$
--
--   and let $D_0$ be any set with $B_{2\delta}(x_0)\cap D^-\subseteq D_0$. For every $k>0$, with $\Phi_k(x,y)=\frac i4H_0^{(1)}(k|x-y|)$,
--
--   $$\sup_{j\ge1}\ \big\|\Phi_k(\cdot,x_j)\big\|_{H^1(D_0)}=\infty .$$
--
--   The gradient of $\Phi_k(\cdot,x_j)$ has the same $\frac1{2\pi|x-x_j|}$ singularity as that of $\Phi_0$, which is not uniformly square integrable on a cone below $x_0$ as $x_j\to x_0$. This is the blow-up used for the contradiction in part (i) of the proof of Theorem 6.1.
--
--   **Formalization Note** The unboundedness is stated as: for every real $C$ some $j\ge1$ has $\|\Phi_k(\cdot,x_j)\|_{H^1(D_0)}>C$, with the platform's `h1Norm`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, part (i), PDF p. 23 ("‖Φ_{k_+}(x, x_j)‖_{H^1(D_0)} → ∞ as j → ∞"); Φ_k: Section 2, p. 4.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem helmholtz_h1_blowup (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (s0 δ : ℝ) (hδ : 0 < δ)
    (D0 : Set R2) (hD0 : Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0)
    (k : ℝ) (hk : 0 < k) :
    ∀ C : ℝ, ∃ j : ℕ, 1 ≤ j ∧ ENNReal.ofReal C <
      h1Norm D0 (fun x => Phi k x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) := by sorry

end RoughSurfaceScattering
