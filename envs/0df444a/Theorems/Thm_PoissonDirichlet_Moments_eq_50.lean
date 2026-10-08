-- Prove2me | Theorems.Thm_PoissonDirichlet_Moments_eq_50
-- name    : PoissonDirichlet.Moments.eq_50
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:47.619698+00:00
-- url     : https://prove2.me/theorems/995b9443-9d0c-470f-a693-356e90f04cfb
-- title:
--   (50), p. 867 — n^{p/α}E_{α,θ}(V_n^p) → C_{α,θ}/C_{α,θ+p}
-- statement:
--   Let $0<\alpha<1$, $\theta>-\alpha$, $p>0$, and let $(V_n)$ have the $\mathrm{PD}(\alpha,\theta)$ law. Then, as $n\to\infty$,
--
--   $$n^{p/\alpha}E_{\alpha,\theta}\big(V_n^p\big)\longrightarrow\frac{C_{\alpha,\theta}}{C_{\alpha,\theta+p}},$$
--
--   where $C_{\alpha,\theta}=\dfrac{\Gamma(\theta+1)}{\Gamma(\theta/\alpha+1)}\Gamma(1-\alpha)^{\theta/\alpha}$ is the constant of (43).
--
--   The limit is the $p$-th moment of $L^{1/\alpha}$ under $P_{\alpha,\theta}$, the almost sure limit of $n^{1/\alpha}V_n$; the statement describes the decay $V_n\approx (L/n)^{1/\alpha}$ in mean.
--
--   **Formalization Note** Indexing is from $0$: the Lean sequence index $k$ is $n-1$, and $n=k+1$ appears in the factor $n^{p/\alpha}$. $C_{\alpha,\theta+p}>0$ since $\theta+p>-\alpha$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 867, (50)

import Mathlib
import Definitions.Def_PoissonDirichlet_Moments_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Moments

/-- (50), p. 867, 0-based (`n = k + 1`): for `0 < α < 1`, `θ > -α`, `p > 0`, under `PD(α, θ)`,
`n^{p/α} E(V_n^p) → C_{α,θ} / C_{α,θ+p}` as `n → ∞`. -/
theorem eq_50 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α θ P V)
    (p : ℝ) (hp : 0 < p) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ (p / α) * ∫ ω, V ω k ^ p ∂P) atTop
      (𝓝 (pdConst α θ / pdConst α (θ + p))) := by sorry

end PoissonDirichlet.Moments
