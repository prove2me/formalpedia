-- Prove2me | Theorems.Thm_PoissonDirichlet_Chain_eq_30
-- name    : PoissonDirichlet.Chain.eq_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:42.046571+00:00
-- url     : https://prove2.me/theorems/29504d2d-76da-4b89-a1a3-0a5c4c3d8b98
-- title:
--   Display (30), p. 863 — E(L^p) = Γ(p + 1)Γ(1 − α)^{−p}/Γ(pα + 1) for p > −1 under PD(α, 0)
-- statement:
--   Let $0 < \alpha < 1$, suppose $(V_n)$ has the $\mathrm{PD}(\alpha, 0)$ distribution, and let $L = \lim_{n\to\infty} nV_n^\alpha$ be its local time (24). Then for every $p > -1$
--   $$E(L^p) = \frac{\Gamma(p+1)}{\Gamma(p\alpha+1)}\,\Gamma(1-\alpha)^{-p}.$$
--
--   These moments determine the law of $L$ ($\Gamma(1-\alpha)L$ is Mittag-Leffler$(\alpha)$). With $p = \theta/\alpha$ they give the second expression of $C_{\alpha,\theta}$ in (43), which is how the second equality of (140) in Theorem 38 is obtained.
--
--   **Formalization Note.** The middle expression $C^pE(\Sigma^{-\alpha p})$ of (30) involves the stable variable $\Sigma$ of Proposition 10 (ii), which this mission does not define; it is omitted. The right side is positive, so the statement cannot hold through a vanishing (non-integrable) Bochner integral.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 863, (30)

import Mathlib
import Definitions.Def_PoissonDirichlet_Chain_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Chain
/-- (30), p. 863: under `PD(α, 0)`, `0 < α < 1`, the local time `L = lim n V_n^α` of (24) has
moments `E(L^p) = Γ(p + 1) / Γ(pα + 1) · Γ(1 - α)^{-p}` for every `p > -1`. -/
theorem eq_30 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α 0 P V) (L : Ω → ℝ)
    (hL : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ((k : ℝ) + 1) * V ω k ^ α) atTop (𝓝 (L ω)))
    (p : ℝ) (hp : -1 < p) :
    ∫ ω, L ω ^ p ∂P = Real.Gamma (p + 1) / Real.Gamma (p * α + 1) * Real.Gamma (1 - α) ^ (-p) := by sorry

end PoissonDirichlet.Chain
