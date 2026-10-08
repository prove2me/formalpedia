-- Prove2me | Theorems.Thm_PoissonDirichlet_ChainLimit_sigma_clt
-- name    : PoissonDirichlet.ChainLimit.sigma_clt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:58.577914+00:00
-- url     : https://prove2.me/theorems/d64e0c49-94a3-454e-9503-eb88130a80db
-- title:
--   §7.3: central limit theorem for Σ_n/n
-- statement:
--   Let $0<\alpha<1$ and $(V_n)\sim\mathrm{PD}(\alpha,0)$. With $\Sigma_n=(V_{n+1}+V_{n+2}+\cdots)/V_n$, the laws converge weakly as $n\to\infty$:
--   $$\sqrt n\left(\frac{\Sigma_n}{n}-\frac{\alpha}{1-\alpha}\right)\ \Longrightarrow\ N\!\left(0,\frac{\alpha}{(2-\alpha)(1-\alpha)^2}\right).$$
--   This is the distributional input for the fluctuation statement of Proposition 44.
--
--   **Formalization Note** Lean writes the positive variance as `Real.toNNReal` of the displayed real expression. It is strictly positive for $0<\alpha<1$. The index $n=k+1$ avoids a division by zero at the first Lean index.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 890, §7.3, central-limit display

import Mathlib
import Definitions.Def_PoissonDirichlet_ChainLimit_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.ChainLimit

/-- The central-limit claim of §7.3, p. 890, for `Σₙ/n`, with the variance
printed there. The use of `k+1` preserves the paper's `n ≥ 1` index. -/
theorem sigma_clt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (V : Ω → ℕ → ℝ) (hV : HasPD α 0 P V) :
    TendstoInDistribution
      (fun k : ℕ => fun ω : Ω =>
        Real.sqrt ((k : ℝ) + 1) *
          (Sigseq (V ω) k / ((k : ℝ) + 1) - α / (1 - α)))
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal (α / ((2 - α) * (1 - α) ^ 2)))) := by sorry

end PoissonDirichlet.ChainLimit
