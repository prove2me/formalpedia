-- Prove2me | Theorems.Thm_PoissonDirichlet_Moments_proposition_17
-- name    : PoissonDirichlet.Moments.proposition_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:59.63523+00:00
-- url     : https://prove2.me/theorems/d6b37cca-6773-454e-b3fe-c36214b5d68c
-- title:
--   Proposition 17, p. 866 — E_{α,θ}(V_n^p) as one integral of φ_α and ψ_α, (49)
-- statement:
--   Let $0<\alpha<1$, $\theta>-\alpha$, $p>0$ with $\theta+p>0$, and let $(V_n)$ have the two-parameter Poisson–Dirichlet law $\mathrm{PD}(\alpha,\theta)$. For every $n=1,2,\dots$,
--
--   $$E_{\alpha,\theta}\big(V_n^p\big)=\frac{\Gamma(1-\alpha)^{\theta/\alpha}}{\Gamma(n)}\,\frac{\Gamma(\theta+1)}{\Gamma(\theta+p)}\,\frac{\Gamma(\theta/\alpha+n)}{\Gamma(\theta/\alpha+1)}\int_0^\infty t^{p+\theta-1}e^{-t}\phi_\alpha(t)^{n-1}\psi_\alpha(t)^{-\theta/\alpha-n}\,dt,$$
--
--   where $\phi_\alpha(t)=\alpha\int_1^\infty e^{-tx}x^{-\alpha-1}dx$ and $\psi_\alpha(t)=1+\alpha\int_0^1(1-e^{-tx})x^{-\alpha-1}dx$ are (33) and (34).
--
--   This gives every moment of the $n$-th largest frequency of a $\mathrm{PD}(\alpha,\theta)$ random discrete distribution as a single one-dimensional integral, and through $\alpha\downarrow0$ recovers the known formula for $\mathrm{PD}(0,\theta)$ (Corollary 18).
--
--   **Formalization Note** The hypothesis $\theta+p>0$ is not printed in the paper; it is necessary. When $\theta\ge0$ it follows from $p>0$. When $-\alpha<\theta<0$ and $p\le-\theta$, the left side is at most $1$, while the $t$-integral diverges at $0$ (the integrand behaves like $t^{p+\theta-1}$) and $\Gamma(\theta+p)$ is at a pole or negative, so the printed formula has no meaning. Indexing is from $0$: the Lean index $k$ is $n-1$. $\psi_\alpha(t)\ge1$, so the real power $\psi_\alpha(t)^{-\theta/\alpha-n}$ is well defined.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 866, Proposition 17, (49)

import Mathlib
import Definitions.Def_PoissonDirichlet_Moments_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Moments

/-- Proposition 17, p. 866, (49), 0-based (`n = k + 1`): for `0 < α < 1`, `θ > -α`, `p > 0`
(and `θ + p > 0`, a disclosed necessary addition), under `PD(α, θ)`,
`E(V_n^p) = Γ(1-α)^{θ/α}/Γ(n) · Γ(θ+1)/Γ(θ+p) · Γ(θ/α+n)/Γ(θ/α+1)
  · ∫_0^∞ t^{p+θ-1} e^{-t} φ_α(t)^{n-1} ψ_α(t)^{-θ/α-n} dt`. -/
theorem proposition_17 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α θ P V)
    (p : ℝ) (hp : 0 < p) (hθp : 0 < θ + p) (k : ℕ) :
    ∫ ω, V ω k ^ p ∂P =
      Real.Gamma (1 - α) ^ (θ / α) / Real.Gamma ((k : ℝ) + 1)
        * (Real.Gamma (θ + 1) / Real.Gamma (θ + p))
        * (Real.Gamma (θ / α + ((k : ℝ) + 1)) / Real.Gamma (θ / α + 1))
        * ∫ t in Set.Ioi (0 : ℝ), t ^ (p + θ - 1) * Real.exp (-t) * PoissonDirichlet.Wendel.phi α t ^ k *
            PoissonDirichlet.Wendel.psi α t ^ (-(θ / α) - ((k : ℝ) + 1)) := by sorry

end PoissonDirichlet.Moments
