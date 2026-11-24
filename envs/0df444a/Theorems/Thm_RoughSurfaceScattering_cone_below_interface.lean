-- Prove2me | Theorems.Thm_RoughSurfaceScattering_cone_below_interface
-- name    : RoughSurfaceScattering.cone_below_interface
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T04:23:28.430806+00:00
-- url     : https://prove2.me/theorems/f0de46a1-2665-40bd-a5bf-0741c4b06528
-- title:
--   A cone around the normal lies below the interface near each point
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be differentiable at $s_0$, let $\Gamma$ be its graph, $D^-=\{x:x_2<f(x_1)\}$, $x_0=(s_0,f(s_0))$, and let
--
--   $$n(x_0)=\frac{(f'(s_0),-1)}{\sqrt{1+f'(s_0)^2}}$$
--
--   be the unit normal at $x_0$ pointing into $D^-$. Then there is $r>0$ such that
--
--   $$x_0+v\in D^-\qquad\text{whenever }0<|v|<r\ \text{and}\ |v|\le2\,v\cdot n(x_0).$$
--
--   The condition $|v|\le 2\,v\cdot n(x_0)$ says that $v$ makes an angle of at most $60^\circ$ with the normal. So $D^-$ contains a truncated closed cone with vertex $x_0$ and axis $n(x_0)$.
--
--   This is the geometric input behind the blow-up of the singular fields $\Phi(\cdot,x_j)$ with $x_j=x_0-\frac\delta jn(x_0)$ on $B_{2\delta}(x_0)\cap D^-$, as used in Theorems 5.2, 5.3 and in Section 6. On this cone, $|x-x_j|$ is comparable to $(x-x_j)\cdot n(x_0)$. Since the cone condition is invariant under positive dilations of $v$, it is well suited to dyadic estimates of singular integrals.
--
--   **Formalization Note** Only differentiability of $f$ at $s_0$ is assumed; no global regularity of the interface is needed. The inner product is the Euclidean one on $\mathbb R^2$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2: geometric fact used implicitly in Theorems 5.2, 5.3 (PDF pp. 17–22) and in the proof of Theorem 6.1 (PDF pp. 22–25), where B_{2δ}(x_0) ∩ D^- is used as a region on which the singular fields Φ(·, x_j), x_j = x_0 − (δ/j) n(x_0), concentrate; n(x_0) and D^-: Section 2, p. 4.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem cone_below_interface (f : ℝ → ℝ) (s0 : ℝ) (hf : DifferentiableAt ℝ f s0) :
    ∃ r > (0 : ℝ), ∀ v : R2, v ≠ 0 → ‖v‖ < r →
      ‖v‖ ≤ 2 * @inner ℝ R2 _ v (normal f s0) → gpt f s0 + v ∈ Dminus f := by sorry

end RoughSurfaceScattering
