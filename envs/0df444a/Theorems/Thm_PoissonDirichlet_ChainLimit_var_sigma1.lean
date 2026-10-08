-- Prove2me | Theorems.Thm_PoissonDirichlet_ChainLimit_var_sigma1
-- name    : PoissonDirichlet.ChainLimit.var_sigma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:13.381833+00:00
-- url     : https://prove2.me/theorems/96e4ec47-63bb-4960-bbe1-5bd2266f4c95
-- title:
--   §7.3: Var_{α,0}(Σ₁) = α/((2 − α)(1 − α)²)
-- statement:
--   Let $0<\alpha<1$ and $(V_n)\sim\mathrm{PD}(\alpha,0)$. The variable $\Sigma_1=(V_2+V_3+\cdots)/V_1$ has a finite second moment and
--   $$\operatorname{Var}_{\alpha,0}(\Sigma_1)=\frac{\alpha}{(2-\alpha)(1-\alpha)^2}.$$
--   This is the Gaussian variance in the central-limit statement for $\Sigma_n/n$.
--
--   **Formalization Note** Square integrability is included in the conclusion to exclude a fallback value for variance.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 890, §7.3, displayed variance of Σ₁

import Mathlib
import Definitions.Def_PoissonDirichlet_ChainLimit_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.ChainLimit

/-- The variance displayed at the end of p. 890. The `L²` clause ensures the
variance is an ordinary finite variance, not a fallback value. -/
theorem var_sigma1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (V : Ω → ℕ → ℝ) (hV : HasPD α 0 P V) :
    MemLp (fun ω => Sigseq (V ω) 0) 2 P ∧
      variance (fun ω => Sigseq (V ω) 0) P =
        α / ((2 - α) * (1 - α) ^ 2) := by sorry

end PoissonDirichlet.ChainLimit
