-- Prove2me | Theorems.Thm_RUCVaR_MinFormula_tail_distribution
-- name    : RUCVaR.MinFormula.tail_distribution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:53.587971+00:00
-- url     : https://prove2.me/theorems/4f6d44d4-1943-4877-847a-1d8dd5a16188
-- title:
--   Note after Definition 3, p. 7 — Ψ_β(x, ·) is a distribution function; the β-tail distribution exists and has a finite mean
-- statement:
--   Let $P$ be a probability measure on $\mathbb R^m$, let $x$ be a decision whose loss $y\mapsto f(x,y)$ is measurable and integrable, and let $0<\beta<1$. Let $\Psi_\beta(x,\cdot)$ be the β-tail distribution function (8),
--   $$
--   \Psi_\beta(x,\alpha)=\begin{cases}0 & \alpha<\alpha_\beta(x),\\ [\Psi(x,\alpha)-\beta]/[1-\beta] & \alpha\ge\alpha_\beta(x).\end{cases}
--   $$
--   Then:
--
--   1. $\Psi_\beta(x,\cdot)$ is nondecreasing;
--   2. $\Psi_\beta(x,\cdot)$ is right-continuous at every point;
--   3. $\Psi_\beta(x,\alpha)\to1$ as $\alpha\to\infty$;
--   4. the β-tail distribution of Definition 3 exists: it is a probability measure on $\mathbb R$ whose distribution function is $\Psi_\beta(x,\cdot)$;
--   5. its mean is finite (the identity is integrable against it).
--
--   The note on p. 7 is what makes Definition 3 meaningful: the β-CVaR $\phi_\beta(x)$ is the mean of this measure.
--
--   **Formalization Note** Items 4 and 5 are the formal content of "the β-tail distribution referred to in (7) is thus well defined through (8)": in Lean the β-CVaR is the integral of the identity against a chosen measure with this distribution function, and that integral is meaningful only once such a measure exists and is integrable. The theorem takes measurability and integrability of the single loss $f(x,\cdot)$ instead of the paper's standing assumptions for all $x$, which makes it stronger.
-- source:
--   Rockafellar & Uryasev, Conditional value-at-risk for general loss distributions, Research Report #2001-5, Univ. of Florida, April 4, 2001, p. 7, note after Definition 3, (7)–(8)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RUCVaR_MinFormula_Setting
open MeasureTheory Filter Topology

namespace RUCVaR.MinFormula

/-- Note after Definition 3, p. 7: `Ψ_β(x, ·)` is a distribution function, so the β-tail
distribution of (7)–(8) exists; its mean is finite. -/
theorem tail_distribution {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin n → ℝ) (hmeas : Measurable (f x))
    (hint : Integrable (f x) P) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Monotone (PsiBeta P f β x) ∧
    (∀ a : ℝ, ContinuousWithinAt (PsiBeta P f β x) (Set.Ici a) a) ∧
    Tendsto (PsiBeta P f β x) atTop (𝓝 1) ∧
    IsBetaTailDistribution P f β x (tailDist P f β x) ∧
    Integrable (fun z : ℝ => z) (tailDist P f β x) := by sorry

end RUCVaR.MinFormula
