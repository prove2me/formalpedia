-- Prove2me | Theorems.Thm_ParallelLpSCO_EpochDA_lemma_1_moment
-- name    : ParallelLpSCO.EpochDA.lemma_1_moment
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:24:03.760757+00:00
-- url     : https://prove2.me/theorems/d7d35939-7b0a-44d9-90ca-fe250ba57350
-- title:
--   Lemma 1, first bullet, under the moment bound $\mathbb E\|g(z)\|_q^q\le G^q$ (corrected: the expectation needs a moment hypothesis)
-- statement:
--   **Source** (Lemma 1, first bullet): for $f$ convex and a gradient estimator $g$ with $\mathbb{E}[g]$ in the subdifferential of $f$, the $p$-GREG estimator satisfies $\mathbb{E}[\text{estimator}] = \nabla \hat f_{\rho,p}(x)$.
--
--   **Variant:** if in addition $\mathbb{E}\|g(z)\|_q^q \le G^q$ for all $z$ (some $G \ge 0$), then the estimator is integrable under $\mathcal{GG}_p(0, \rho^2) \times \mathrm{Unif}[0, 1]$ and $\hat f_{\rho,p}$ is Fréchet differentiable at $x$ with derivative $h \mapsto \langle \mathbb{E}[\text{estimator}], h \rangle$.
--
--   **Difference:** the variant adds the second bullet's moment hypothesis to the first bullet; without it the expectation can diverge (I5).
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), p. 7, Lemma 1 (corrected)

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics

open MeasureTheory

namespace ParallelLpSCO.EpochDA

theorem lemma_1_moment (p : ℝ) (hp : 2 ≤ p) (d : ℕ) (f : Vec d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (g : Oracle d) (hgm : Measurable (Function.uncurry g))
    (hg : ∀ z, IsSubgrad f z (∫ u, g z u))
    (G : ℝ) (hG : 0 ≤ G) (hmom : ∀ z, qMoment p g z ≤ ENNReal.ofReal (G ^ conjExp p))
    (ρ : ℝ) (hρ : 0 < ρ) (xbar x : Vec d) :
    let μ : Measure (Vec d × unitInterval) := (ggLaw d p ρ).prod (volume : Measure unitInterval)
    let est : Vec d × unitInterval → Vec d := fun ξu => pgreg p ρ xbar x ξu.1 (g (xbar + ξu.1) ξu.2)
    Integrable est μ ∧
      HasFDerivAt (fHat p ρ f)
        (∑ i, (∫ ξu, est ξu ∂μ) i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)
        x := by sorry

end ParallelLpSCO.EpochDA
