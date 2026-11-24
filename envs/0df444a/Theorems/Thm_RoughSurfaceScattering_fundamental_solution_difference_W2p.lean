-- Prove2me | Theorems.Thm_RoughSurfaceScattering_fundamental_solution_difference_W2p
-- name    : RoughSurfaceScattering.fundamental_solution_difference_W2p
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T20:57:37.946262+00:00
-- url     : https://prove2.me/theorems/af815416-9d3d-4606-a619-b63dd1e22cd4
-- title:
--   Lemma 5.1: $\Phi_{k_1}(\cdot,y)-\Phi_k(\cdot,y)\in W^{2,p}(B_1(y))$
-- statement:
--   Let $y\in\mathbb R^2$, $k,k_1\ge0$ and $1\le p<\infty$, where $\Phi_0(x,y)=\frac1{2\pi}\ln\frac1{|x-y|}$ and $\Phi_k(x,y)=\frac i4H_0^{(1)}(k|x-y|)$ for $k>0$. Then
--
--   $$\Phi_{k_1}(\cdot,y)-\Phi_k(\cdot,y)\in W^{2,p}(B_1(y)).$$
--
--   The logarithmic singularities of the two fundamental solutions cancel, leaving a function whose second derivatives are $O(|\ln|x-y||)$ near $y$. This is used to show that differences of point-source fields of different wave numbers produce uniformly bounded boundary data.
--
--   **Formalization Note** $W^{2,p}(B_1(y))$ is defined directly through weak derivatives of orders one and two tested against $C_c^\infty(B_1(y))$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, claim c005; Section 5, Lemma 5.1, PDF p. 17 (fundamental solutions: Section 2, p. 4)

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem fundamental_solution_difference_W2p (y : R2) (k k1 : ℝ) (hk : 0 ≤ k) (hk1 : 0 ≤ k1)
    (p : ENNReal) (hp1 : 1 ≤ p) (hp : p ≠ ⊤) :
    MemW2p (Metric.ball y 1) p (fun x => Phi k1 x y - Phi k x y) := by sorry

end RoughSurfaceScattering
