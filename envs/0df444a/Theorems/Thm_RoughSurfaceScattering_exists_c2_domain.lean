-- Prove2me | Theorems.Thm_RoughSurfaceScattering_exists_c2_domain
-- name    : RoughSurfaceScattering.exists_c2_domain
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T02:15:42.341437+00:00
-- url     : https://prove2.me/theorems/5ebcd903-a142-56cf-8187-c880a67705f3
-- title:
--   A $C^{2,\lambda}$ domain below $\Gamma$ containing $B_{2\delta}(x_0)\cap D^-$
-- statement:
--   Let $f\in BC^{1,1}\cap C^{2,\lambda}$, $x_0=(s_0,f(s_0))$ and $\delta>0$. There is a bounded $C^{2,\lambda}$ domain $D_0$ with
--   $$B_{2\delta}(x_0)\cap D^-\subseteq D_0\subseteq D^- .$$
--   Take the region below the graph over a long interval and round it off smoothly away from $B_{2\delta}(x_0)$. Its boundary near $x_0$ is the graph of $f$.
--
--   **Formalization Note** Domains are the platform's `IsC2LambdaDomain`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1, PDF pp. 22-24 ('Since f ∈ C^{2,α}(ℝ), there exists a small C^{2,λ} bounded domain D_0 ...', p. 23).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem exists_c2_domain (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1)
    (hf' : IsC2Lambda lam f) (s0 δ : ℝ) (hδ : 0 < δ) :
    ∃ D0 : Set R2, IsC2LambdaDomain lam D0 ∧
      Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 ∧ D0 ⊆ Dminus f := by sorry

end RoughSurfaceScattering
