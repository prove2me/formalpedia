-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem54
-- name    : ShockWear.Inherit.Supplement.theorem54
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T23:56:37.361889+00:00
-- url     : https://prove2.me/theorems/0ad19b7f-b0ed-4d8b-ab4d-97e34fa3b23d
-- title:
--   Theorem 5.4 — PF₂ damage and threshold densities give decreasing failure ratios and PF₂ life density
-- statement:
--   Let $F$ and $G$ be probability distributions with $F(z)=0$ for $z<0$ and $G(0)=0$. Suppose they have chosen PF₂ densities $f$ and $g$. For $\bar P_k=\int F^{(k)}(x)\,dG(x)$ and $\lambda>0$, both conclusions hold:
--
--   $$
--   \frac{\bar P_k-\bar P_{k+1}}{\bar P_{k-1}-\bar P_k}\text{ decreases for }k\ge1,
--   \qquad h\text{ is PF}_2\text{ on }(0,\infty),
--   $$
--
--   where $h$ is the positive-time density (2.3) of the random-threshold mixture (5.2). This retains the complete ratio assertion together with its life-density consequence.
--
--   **Formalization Note** The source states PF₂ density versions; we state that the chosen nonnegative Lebesgue-measurable versions induce the measures and have TP₂ real difference kernels. The coefficients are the published literal `randP` integral. Ratios use the published all-pairs cross-product predicate on failure indices starting at one. Since $G$ has a density, the p. 642 common-discontinuity issue is absent.
--
--   Differences from the source:
--   - encoding: nonnegative damage distribution F and threshold distribution G with G(0)=0 → probability measures μ,ν on ℝ with μ(−∞,0)=0 and ν(−∞,0]=0; reason: CDFs are masses of closed lower intervals; all atoms and nonnegative damage laws are represented
--   - encoding: a chosen PF₂ density version → a nonnegative Lebesgue-measurable density inducing the law and a TP₂ difference kernel; reason: this is Definition 2.3 applied to the chosen version; no moment, smoothness or strict-positivity condition is added
--   - encoding: successive ratios on their nonzero-denominator domain → all ordered cross-product inequalities on the nonnegative sequence; reason: this is the zero-compatible log-convex or PF₂ ratio convention; no division-by-zero value is used, and no inference from adjacent ratios across gaps is assumed
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 646, Theorem 5.4; https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_RandThreshold_Model
import Definitions.Def_ShockWear_Inherit_Supplement_TotalPositivity
import Definitions.Def_ShockWear_Inherit_Supplement_Density

namespace ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem54 (lam : ℝ) (hlam : 0 < lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iic 0) = 0)
    (f g : ℝ → ℝ) (hf : IsDensity μ f) (hg : IsDensity ν g)
    (hpf : IsPF2Function f) (hpg : IsPF2Function g) :
    IsPF2SeqFrom 1 (failProb (ShockWear.RandThreshold.randP μ ν)) ∧
    IsPF2Dens (shockDens lam (ShockWear.RandThreshold.randP μ ν)) := by sorry

end ShockWear.Inherit.Supplement
