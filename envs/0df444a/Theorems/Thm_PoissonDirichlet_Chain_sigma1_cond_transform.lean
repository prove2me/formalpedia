-- Prove2me | Theorems.Thm_PoissonDirichlet_Chain_sigma1_cond_transform
-- name    : PoissonDirichlet.Chain.sigma1_cond_transform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:00:11.243041+00:00
-- url     : https://prove2.me/theorems/1969a21b-bb27-4190-8eeb-4cb21b5e6afc
-- title:
--   Proof of Theorem 38 (iii), p. 889 — X_1 = LV_1^{−α} is exponential(1) and E_{α,0}[exp(−λΣ_1)|X_1] = exp[−X_1(ψ_α(λ) − 1)]
-- statement:
--   Let $0 < \alpha < 1$, suppose $(V_n)$ has the $\mathrm{PD}(\alpha, 0)$ distribution, let $L = \lim_n nV_n^\alpha$ (24) and $\Sigma_1 = (V_2 + V_3 + \cdots)/V_1$ (32). Then $X_1 = LV_1^{-\alpha}$ has the exponential distribution with rate 1, and for every $\lambda \ge 0$
--   $$E_{\alpha,0}\big[\exp(-\lambda\Sigma_1) \mid X_1\big] = \exp\big[-X_1(\psi_\alpha(\lambda) - 1)\big].$$
--
--   Together with (145) this gives the Laplace transform (141) of Theorem 38 (iii).
--
--   **Formalization Note.** The conditional expectation is stated in its defining form: for every nonnegative measurable $g$, $E[e^{-\lambda\Sigma_1}g(X_1)] = E[e^{-X_1(\psi_\alpha(\lambda)-1)}g(X_1)]$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 889, proof of Theorem 38 (iii), display after (147); from (68), p. 871

import Mathlib
import Definitions.Def_PoissonDirichlet_Chain_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Chain
/-- Proof of Theorem 38 (iii), p. 889: under `PD(α, 0)`, `0 < α < 1`, with `L` the local time
(24), `X_1 = L V_1^{-α}` has the exponential distribution with rate 1, and, from (68),
`E_{α,0}[exp(-λΣ_1) | X_1] = exp[-X_1(ψ_α(λ) - 1)]` for `λ ≥ 0`, where
`Σ_1 = (V_2 + V_3 + ⋯)/V_1` (32). The conditional expectation is stated through its defining
property: the identity holds after multiplying by `g(X_1)` and integrating, for every nonnegative
measurable `g`. -/
theorem sigma1_cond_transform {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (V : Ω → ℕ → ℝ)
    (hV : PoissonDirichlet.Ratio.HasPD α 0 P V) (L : Ω → ℝ)
    (hL : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ((k : ℝ) + 1) * V ω k ^ α) atTop (𝓝 (L ω))) :
    HasLaw (fun ω => L ω * V ω 0 ^ (-α)) (expMeasure 1) P ∧
    ∀ l : ℝ, 0 ≤ l → ∀ g : ℝ → ENNReal, Measurable g →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-l * PoissonDirichlet.Wendel.Sigseq (V ω) 0)) * g (L ω * V ω 0 ^ (-α)) ∂P =
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-(L ω * V ω 0 ^ (-α)) * (PoissonDirichlet.Wendel.psi α l - 1))) *
          g (L ω * V ω 0 ^ (-α)) ∂P := by sorry

end PoissonDirichlet.Chain
