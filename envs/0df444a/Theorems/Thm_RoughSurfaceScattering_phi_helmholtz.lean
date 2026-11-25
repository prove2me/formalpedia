-- Prove2me | Theorems.Thm_RoughSurfaceScattering_phi_helmholtz
-- name    : RoughSurfaceScattering.phi_helmholtz
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T08:18:52.063907+00:00
-- url     : https://prove2.me/theorems/69fca7be-e692-5bfe-89da-f9c33b0d8c6e
-- title:
--   $\Phi_k(\cdot,z)$ solves the Helmholtz equation $\Delta u+k^2u=0$ away from $z$
-- statement:
--   For every $k\ge0$ and $z\in\mathbb R^2$, the fundamental solution $\Phi_k(\cdot,z)$ satisfies
--
--   $$\Delta\Phi_k(\cdot,z)+k^2\,\Phi_k(\cdot,z)=0\qquad\text{on }\mathbb R^2\setminus\{z\}.$$
--
--   For $k=0$, $\Phi_0=\frac1{2\pi}\ln\frac1{|x-z|}$ is harmonic. For $k>0$, $\Phi_k=\frac i4H_0^{(1)}(k|x-z|)$ is given by the platform's power-series definitions of $J_0$ and $Y_0$. The statement then reduces to Bessel's equation for these series: $J_0$ satisfies it, and the series part of $Y_0$ compensates the logarithm.
--
--   **Formalization Note** The Laplacian is Mathlib's `Laplacian.laplacian`, through the platform's `IsHelmholtzOn`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 2, p. 4: Φ_k(x,y) = (i/4)H_0^{(1)}(k|x−y|) is the fundamental solution of the Helmholtz equation (Φ_0 for the Laplace equation). Needed for the radiating solutions used in Lemma 2.4 and Theorems 5.2-5.3.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem phi_helmholtz (k : ℝ) (hk : 0 ≤ k) (z : R2) :
    IsHelmholtzOn {x | x ≠ z} k (fun x => Phi k x z) := by sorry

end RoughSurfaceScattering
