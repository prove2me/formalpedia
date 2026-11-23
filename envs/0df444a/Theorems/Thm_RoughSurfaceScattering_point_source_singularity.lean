-- Prove2me | Theorems.Thm_RoughSurfaceScattering_point_source_singularity
-- name    : RoughSurfaceScattering.point_source_singularity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:58:12.296804+00:00
-- url     : https://prove2.me/theorems/51603af8-be30-475d-a59f-8584660deb71
-- title:
--   Theorem 5.2: $H^1$ singularity of the transmitted field for a point source
-- statement:
--   Let $f\in BC^{1,1}(\mathbb R)\cap C^{2,\lambda}(\mathbb R)$ with $\lambda\in(0,1]$, and let $k_\pm,\mu>0$ satisfy $(\mu-1)(k_+^2-k_-^2\mu)\ge0$ and $k_+^2\ne k_-^2\mu$. Let $x_0\in\Gamma$. There is $\delta_0>0$ such that for every $\delta\in(0,\delta_0)$ the points
--
--   $$x_j:=x_0-\frac\delta j\,n(x_0),\qquad j=1,2,\dots$$
--
--   lie in $D^+$, and the following holds. Let $D_0$ be a bounded $C^{2,\lambda}$ domain with $B_{2\delta}(x_0)\cap D^-\subseteq D_0\subseteq D^-$, and let $(u_+^{(j)},u_-^{(j)})$ solve the TSP with incident point source $u^i_j=\Phi_{k_+}(\cdot,x_j)$, i.e. with data $g_1=-u^i_j|_\Gamma$, $g_2=-\partial_nu^i_j|_\Gamma$. Then there is $C>0$ independent of $j$ with
--
--   $$\Big\|u_-^{(j)}-\frac2{\mu+1}\Phi_0(\cdot,x_j)\Big\|_{H^1(D_0)}\le C\qquad(j\ge1).$$
--
--   So, as the source approaches the interface, the transmitted field has the singularity of $\frac2{\mu+1}\Phi_0(\cdot,x_j)$ in $H^1(D_0)$.
--
--   **Formalization Note** "$\delta>0$ small enough" is stated as the existence of a threshold $\delta_0$. The TSP solutions, unique by Theorem 3.3, are quantified over, so the bound holds for every family of solutions. The $C^{2,\lambda}$ regularity of $f$ is required globally on $\mathbb R$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, claim c006; Section 5, Theorem 5.2, PDF pp. 17-18

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem point_source_singularity (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hf2 : IsC2Lambda lam f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (s0 : ℝ) :
    ∃ δ0 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ0 →
      (∀ j : ℕ, 1 ≤ j → gpt f s0 - (δ / (j : ℝ)) • normal f s0 ∈ Dplus f) ∧
      ∀ D0 : Set R2, IsC2LambdaDomain lam D0 →
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 → D0 ⊆ Dminus f →
        ∀ u : ℕ → (R2 → ℂ) × (R2 → ℂ),
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp km μ
            (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).1
            (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).2
            (u j).1 (u j).2) →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
            h1Norm D0 (fun x => (u j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
              Phi 0 x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) ≤ ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
