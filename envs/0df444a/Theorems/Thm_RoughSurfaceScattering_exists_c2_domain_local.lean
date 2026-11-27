-- Prove2me | Theorems.Thm_RoughSurfaceScattering_exists_c2_domain_local
-- name    : RoughSurfaceScattering.exists_c2_domain_local
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T02:41:00.472406+00:00
-- url     : https://prove2.me/theorems/56517043-7e38-4dca-b679-6b35e036295c
-- title:
--   Small $C^{2,\lambda}$ domains below $\Gamma$ near a boundary point
-- statement:
--   Let $f\in BC^{1,1}\cap C^{2,\lambda}$ and $x_0=(s_0,f(s_0))$. There is $\delta_1>0$ such that for every $0<\delta<\delta_1$ there is a bounded $C^{2,\lambda}$ domain $D_0$ with
--   $$B_{2\delta}(x_0)\cap D^-\subseteq D_0\subseteq D^-\cap B_{3\delta}(x_0).$$
--   *Proof idea.* For small $\delta$, $B_{3\delta}(x_0)\cap D^-$ is a connected lens bounded by an arc of $\Gamma$ and an arc of a circle. Round off its two corners inside the annulus $2\delta<|x-x_0|<3\delta$ with $C^\infty$ arcs. This gives a $C^{2,\lambda}$ boundary, because $\Gamma$ itself is $C^{2,\lambda}$.
--
--   **Formalization Note** Smallness of $\delta$ ensures connectedness.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1, case Γ1 ≠ Γ2, PDF pp. 22-23 (choice of the small C^{2,λ} domain D_0 ⊂ D^- with B_{2δ}(x_0)∩D^- ⊂ D_0).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem exists_c2_domain_local (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1)
    (hf' : IsC2Lambda lam f) (s0 : ℝ) :
    ∃ δ1 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ1 →
      ∃ D0 : Set R2, IsC2LambdaDomain lam D0 ∧
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 ∧ D0 ⊆ Dminus f ∧
        D0 ⊆ Metric.ball (gpt f s0) (3 * δ) := by sorry

end RoughSurfaceScattering
