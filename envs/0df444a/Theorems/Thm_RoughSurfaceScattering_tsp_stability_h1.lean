-- Prove2me | Theorems.Thm_RoughSurfaceScattering_tsp_stability_h1
-- name    : RoughSurfaceScattering.tsp_stability_h1
-- status  : Open
-- author  : @もち
-- created : 2026-11-25T06:40:20.985977+00:00
-- url     : https://prove2.me/theorems/84b27feb-e879-44c4-94c4-967d3c702ea4
-- title:
--   Theorem 4.3 (stability): $H^1(D_0)$ bound for TSP solutions by the Hölder norms of the data
-- statement:
--   Let $f\in BC^{1,1}$, let the scatterer satisfy `ParamCond`, let $0<\alpha<1$, and let $D_0\subseteq D_-$ be a bounded open set. There is $C$ with the following property. Let $(u_+,u_-)$, $(w_+,w_-)$, $(v_+,v_-)$ be TSP solutions with data $g$, $h$, $k$, such that $g_1-h_1-k_1\in BC^{1,\alpha}(\Gamma)$ and $g_2-h_2-k_2\in BC^{0,\alpha}(\Gamma)$. Then
--
--   $$\|u_--w_--v_-\|_{H^1(D_0)}\le C\big(\|g_1-h_1-k_1\|_{1,\alpha,\Gamma}+\|g_2-h_2-k_2\|_{0,\alpha,\Gamma}\big).$$
--
--   The combination $u-w-v$ solves the TSP with data $g-h-k$:
--   - Each TSP solution is bounded: on the strip by the $BC^1$ condition, and above or below it by the radiation representation.
--   - So condition (iii) holds with $\beta=0$, and the radiation conditions are linear by Lemma 2.4.
--
--   By uniqueness it is therefore the solution of Theorem 4.3. On a strip containing $D_0$, $|u_-|$ and $|\nabla u_-|$ depend continuously on $\|g_1\|_{1,\alpha}$ and $\|g_2\|_{0,\alpha}$. Since $D_0$ is bounded, this gives the $H^1$ bound.
--
--   **Formalization Note** The norms are the platform's `holderNorm1` and `holderNorm0`. Three solutions are combined so that no separate linearity lemma for `IsTSPSolution` is needed.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 4.3 (p. 16-17) together with the uniqueness Theorem 3.3.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem tsp_stability_h1 (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ)
    (hpar : ParamCond kp km μ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (D0 : Set R2)
    (hD0 : IsOpen D0) (hb : Bornology.IsBounded D0) (hsub : D0 ⊆ Dminus f) :
    ∃ C : ℝ, ∀ (g1 g2 h1 h2 k1 k2 : ℝ → ℂ) (up um wp wm vp vm : R2 → ℂ),
      IsTSPSolution f kp km μ g1 g2 up um → IsTSPSolution f kp km μ h1 h2 wp wm →
      IsTSPSolution f kp km μ k1 k2 vp vm →
      IsBC1AlphaGam f α (fun s => g1 s - h1 s - k1 s) →
      IsBC0AlphaGam f α (fun s => g2 s - h2 s - k2 s) →
      h1Norm D0 (fun x => um x - wm x - vm x) ≤
        ENNReal.ofReal (C * (holderNorm1 f α (fun s => g1 s - h1 s - k1 s) +
          holderNorm0 f α (fun s => g2 s - h2 s - k2 s))) := by sorry

end RoughSurfaceScattering
