-- Prove2me | Theorems.Thm_RoughSurfaceScattering_laplace_l2_bound
-- name    : RoughSurfaceScattering.laplace_l2_bound
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T04:01:05.185998+00:00
-- url     : https://prove2.me/theorems/9ef4e5d1-968c-4720-b0e7-84ffc66db109
-- title:
--   $\Phi_0(\cdot,x_j)$ is uniformly bounded in $L^2(D_0)$ on a bounded set
-- statement:
--   Let $D_0\subseteq\mathbb R^2$ be bounded, let $f:\mathbb R\to\mathbb R$, $s_0,\delta\in\mathbb R$, let $x_0=(s_0,f(s_0))$ and let $n(x_0)$ be the vector `normal f s0`. Put $x_j=x_0-\frac\delta j\,n(x_0)$. For every real constant $c$ there is $C$ with
--
--   $$\big\|c\,\Phi_0(\cdot,x_j)\big\|_{L^2(D_0)}\le C\qquad(j\ge1),\qquad \Phi_0(x,y)=\frac1{2\pi}\ln\frac1{|x-y|}.$$
--
--   The logarithmic singularity is square integrable, and since the points $x_j$ stay in a bounded set the bound is uniform in $j$. Together with Theorem 5.2 this shows that the transmitted fields $u_-(\cdot,x_j)$ are bounded in $L^2(D_0)$.
--
--   **Formalization Note** $L^2(D_0)$ is taken for Lebesgue measure restricted to $D_0$. Only boundedness of $D_0$ is assumed.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, part (i), PDF p. 23 ("It follows from Theorem 5.2 and the uniform boundedness of Φ_0(x, x_j) in L^2(D_0) that ‖u_{1,-}^{(j)}‖_{L^2(D_0)} ≤ C").

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem laplace_l2_bound (f : ℝ → ℝ) (s0 δ : ℝ) (D0 : Set R2) (hD0 : Bornology.IsBounded D0)
    (c : ℝ) :
    ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
      l2Norm D0 (fun x => (c : ℂ) * Phi 0 x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) ≤
        ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
