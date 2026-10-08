-- Prove2me | Theorems.Thm_PoissonDirichlet_Moments_corollary_18
-- name    : PoissonDirichlet.Moments.corollary_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:45.797013+00:00
-- url     : https://prove2.me/theorems/e87bdd41-0939-45d8-b30f-17a60f934415
-- title:
--   Corollary 18, p. 867 — E_{0,θ}(V_n^p) for PD(0, θ), (51)
-- statement:
--   Let $\theta>0$, $p>0$, and let $(V_n)$ have the one-parameter Poisson–Dirichlet law $\mathrm{PD}(0,\theta)$. For every $n=1,2,\dots$,
--
--   $$E_{0,\theta}\big(V_n^p\big)=\frac{\Gamma(\theta)}{\Gamma(\theta+p)}\,\frac{\theta^n}{\Gamma(n)}\int_0^\infty t^{p-1}e^{-t}E(t)^{n-1}e^{-\theta E(t)}\,dt,$$
--
--   where $E(t)=\int_t^\infty x^{-1}e^{-x}\,dx$ is the exponential integral.
--
--   This is the known moment formula for the ranked frequencies of Kingman's $\mathrm{PD}(0,\theta)$ law; the paper recovers it from Proposition 17 by letting $\alpha\downarrow0$.
--
--   **Formalization Note** $\theta>0$ is the parameter range of Definition 1 at $\alpha=0$ ($\theta>-\alpha$). At $\alpha=0$ the stick-breaking variables are $\mathrm{beta}(1,\theta)$. Indexing is from $0$: the Lean index $k$ is $n-1$, and $\theta^n$ is $\theta^{k+1}$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 867, Corollary 18, (51)

import Mathlib
import Definitions.Def_PoissonDirichlet_Moments_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Moments

/-- Corollary 18, p. 867, (51), 0-based (`n = k + 1`): for `θ > 0` (the range of Definition 1
at `α = 0`) and `p > 0`, under `PD(0, θ)`,
`E(V_n^p) = Γ(θ)/Γ(θ+p) · θ^n/Γ(n) ∫_0^∞ t^{p-1} e^{-t} E(t)^{n-1} e^{-θE(t)} dt`,
where `E(t) = ∫_t^∞ x^{-1} e^{-x} dx`. -/
theorem corollary_18 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : ℝ) (hθ : 0 < θ) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD 0 θ P V) (p : ℝ) (hp : 0 < p) (k : ℕ) :
    ∫ ω, V ω k ^ p ∂P =
      Real.Gamma θ / Real.Gamma (θ + p) * (θ ^ (k + 1) / Real.Gamma ((k : ℝ) + 1)) *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-t) * expIntE t ^ k *
          Real.exp (-θ * expIntE t) := by sorry

end PoissonDirichlet.Moments
