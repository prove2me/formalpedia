-- Prove2me | Theorems.Thm_PoissonDirichlet_ChainLimit_sigma_slln
-- name    : PoissonDirichlet.ChainLimit.sigma_slln
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:06.850043+00:00
-- url     : https://prove2.me/theorems/1fb99694-4784-460a-98b3-251482acb837
-- title:
--   §7.3: Σ_n/n → α/(1 − α) almost surely
-- statement:
--   Let $0<\alpha<1$ and $(V_n)\sim\mathrm{PD}(\alpha,0)$. With $\Sigma_n=(V_{n+1}+V_{n+2}+\cdots)/V_n$, almost surely
--   $$\frac{\Sigma_n}{n}\longrightarrow\frac{\alpha}{1-\alpha}\qquad(n\to\infty).$$
--   This is the asymptotic input for Proposition 44's almost-sure limit.
--
--   **Formalization Note** Lean's index `k` corresponds to paper index $n=k+1$; the denominator is `k+1`, including at `k=0`.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 890, §7.3, strong-law display

import Mathlib
import Definitions.Def_PoissonDirichlet_ChainLimit_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.ChainLimit

/-- The strong-law display of §7.3, p. 890: `Σₙ/n → α/(1-α)` almost surely.
Here `Σ_{k+1}` is divided by `k+1`, following the paper's one-based index. -/
theorem sigma_slln {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (V : Ω → ℕ → ℝ) (hV : HasPD α 0 P V) :
    ∀ᵐ ω ∂P, Tendsto
      (fun k : ℕ => Sigseq (V ω) k / ((k : ℝ) + 1))
      atTop (𝓝 (α / (1 - α))) := by sorry

end PoissonDirichlet.ChainLimit
