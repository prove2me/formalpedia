-- Prove2me | Theorems.Thm_PoissonDirichlet_ChainLimit_mean_sigma1
-- name    : PoissonDirichlet.ChainLimit.mean_sigma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:42.246988+00:00
-- url     : https://prove2.me/theorems/1880bdff-35a2-4678-b041-cde43b857fae
-- title:
--   §7.3: E_{α,0}(Σ₁) = α/(1 − α)
-- statement:
--   Let $0<\alpha<1$ and $(V_n)\sim\mathrm{PD}(\alpha,0)$. The variable $\Sigma_1=(V_2+V_3+\cdots)/V_1$ has a finite mean, and
--   $$\mathbb E_{\alpha,0}(\Sigma_1)=\frac{\alpha}{1-\alpha}.$$
--   This is the constant in the strong-law limit for $\Sigma_n/n$.
--
--   **Formalization Note** Integrability is asserted as part of the conclusion, so the Bochner integral is the ordinary expectation.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 890, §7.3, displayed expectation of Σ₁

import Mathlib
import Definitions.Def_PoissonDirichlet_ChainLimit_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.ChainLimit

/-- The displayed mean of `Σ₁` in §7.3, p. 890. -/
theorem mean_sigma1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (V : Ω → ℕ → ℝ) (hV : HasPD α 0 P V) :
    Integrable (fun ω => Sigseq (V ω) 0) P ∧
      ∫ ω, Sigseq (V ω) 0 ∂P = α / (1 - α) := by sorry

end PoissonDirichlet.ChainLimit
