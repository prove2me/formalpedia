-- Prove2me | Theorems.Thm_RoughSurfaceScattering_layer_kernels_symm
-- name    : RoughSurfaceScattering.layer_kernels_symm
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T12:16:51.1911+00:00
-- url     : https://prove2.me/theorems/e3b6f0a5-3337-4bd2-93f7-59e2185c6083
-- title:
--   Transposition of the layer-potential kernels on $\Gamma$: $S$ is symmetric and $K$ is the transpose of $K'$
-- statement:
--   Let $\Gamma=\{(s,f(s))\}$ with points $x(s)=(s,f(s))$ and normal $n'$ pointing into $D^+$, and let $G=G_k^{(I)}(\cdot,\cdot;a)$ be the impedance Green's function of eq. (2.8) (with either sign $\sigma$). Then, for all $s,t\in\mathbb R$:
--
--   1. the single-layer kernel is symmetric,
--   $$G\big(x(s),x(t)\big)=G\big(x(t),x(s)\big);$$
--   2. the double-layer kernel is the transpose of the adjoint double-layer kernel,
--   $$\frac{\partial G(x(s),y)}{\partial n'(y)}\Big|_{y=x(t)}=\frac{\partial G(x,x(s))}{\partial n'(x)}\Big|_{x=x(t)} .$$
--
--   In operator form: on $\Gamma$, the single-layer operator $S$ has a symmetric kernel, and the kernel of the double-layer operator $K$ is the transpose of that of $K'$. These relations follow from the symmetry $G(x,y)=G(y,x)$ and are the kernel-level input for reciprocity arguments with the boundary integral operator $\mathcal M$.
--
--   **Formalization Note** The kernels are the platform's `kerGam` and `dnyGam`/`dnxGam`, evaluated at the parameters $s,t$ of the boundary points. No differentiability of $G$ is needed: by symmetry, the two functions being differentiated coincide.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 4, PDF pp. 13–14: kernels of the operators S, K, K' built from G_k^{±(I)} (eq. (2.8)), with normal n' pointing into D^+; transposition relations follow from the symmetry of G_k^{±(I)}.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem layer_kernels_symm (f : ℝ → ℝ) (k a σ : ℝ) (s t : ℝ) :
    kerGam f (Gimp k a σ) s t = kerGam f (Gimp k a σ) t s ∧
      dnyGam f (Gimp k a σ) s t = dnxGam f (Gimp k a σ) t s := by sorry

end RoughSurfaceScattering
