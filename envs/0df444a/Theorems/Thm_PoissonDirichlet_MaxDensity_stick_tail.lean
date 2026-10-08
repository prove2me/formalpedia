-- Prove2me | Theorems.Thm_PoissonDirichlet_MaxDensity_stick_tail
-- name    : PoissonDirichlet.MaxDensity.stick_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:21.006994+00:00
-- url     : https://prove2.me/theorems/187d9c37-2e10-4d2c-8f8a-bf15e748cb55
-- title:
--   Proof of Proposition 19, p. 876 — (Ṽ_2, Ṽ_3, …)/(1 − Ṽ_1) has the stick-breaking law with parameters (α, α + θ), independent of Ṽ_1
-- statement:
--   Let $0 \le \alpha < 1$, $\theta > -\alpha$, and let $\tilde Y_n \sim \mathrm{beta}(1-\alpha, \theta+n\alpha)$ be independent, with stick-breaking sequence $\tilde V$ as in (4). Then the renormalised tail
--   $$\left(\frac{\tilde V_2}{1-\tilde V_1}, \frac{\tilde V_3}{1-\tilde V_1}, \dots\right)$$
--   has the same law as the stick-breaking sequence $(\tilde V_1, \tilde V_2, \dots)$ built from independent $\mathrm{beta}(1-\alpha, (\alpha+\theta) + n\alpha)$ variables, that is, the $P_{\alpha,\alpha+\theta}$ law of $(\tilde V_n)$; and it is independent of $\tilde V_1$.
--
--   This is the self-similarity of stick-breaking used in the proof of Proposition 19; the independence is what allows the conditioning on $\tilde V_1 = x$ in (92).
--
--   **Formalization Note.** The page states only the identity of laws; the independence from $\tilde V_1$ is used in the next line of (92) and is part of Proposition 34, and is stated here as a second conjunct. The law of the stick-breaking sequence is expressed through measures of preimages under `stick`.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 876, §5.1, proof of Proposition 19, sentence before (92)

import Mathlib
import Definitions.Def_PoissonDirichlet_MaxDensity_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Proof of Proposition 19, §5.1, p. 876 (Pitman–Yor 1997): "the consequence of (4) that the
`P_{α,θ}` distribution of `(Ṽ₂, Ṽ₃, …)/(1 - Ṽ₁)` is identical to the `P_{α,α+θ}`
distribution of `(Ṽ₁, Ṽ₂, …)`". In the setting of Definition 1 (0-based: `Ytil k` is
`Ỹ_{k+1}`), the sequence `k ↦ PoissonDirichlet.Ratio.stick Ỹ (k+1) / (1 - Ỹ₁)` has the law of `stick` under the
`(α, α + θ)` law of Definition 1, and it is independent of `Ṽ₁ = Ỹ₁` (the independence is
used in the second line of (92)). -/
theorem stick_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (Ytil : ℕ → Ω → ℝ) (hYm : ∀ k, Measurable (Ytil k)) (hYind : iIndepFun Ytil P)
    (hYlaw : ∀ k : ℕ, HasLaw (Ytil k) (betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) P) :
    (∃ μ : Measure (ℕ → ℝ), PoissonDirichlet.Ratio.IsStickLaw α (α + θ) μ ∧
        ∀ s : Set (ℕ → ℝ), MeasurableSet s →
          P ((fun ω k => PoissonDirichlet.Ratio.stick (fun i => Ytil i ω) (k + 1) / (1 - Ytil 0 ω)) ⁻¹' s) =
            μ (PoissonDirichlet.Ratio.stick ⁻¹' s)) ∧
      IndepFun (fun ω k => PoissonDirichlet.Ratio.stick (fun i => Ytil i ω) (k + 1) / (1 - Ytil 0 ω))
        (Ytil 0) P := by sorry

end PoissonDirichlet.MaxDensity
