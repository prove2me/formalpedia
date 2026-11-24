-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem55
-- name    : ShockWear.Inherit.Supplement.theorem55
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:57:03.477852+00:00
-- url     : https://prove2.me/theorems/02ee4e23-c5d8-4803-8ee5-6903411d4999
-- title:
--   Theorem 5.5 — PF₂ damage CDF and threshold density give all survival inequalities and IHR life
-- statement:
--   Let $F$ and $G$ be probability distributions with $F(z)=0$ for $z<0$ and $G(0)=0$. Suppose the CDF $F$ is PF₂ and $G$ has a chosen PF₂ density $g$. For $\bar P_k=\int F^{(k)}(x)\,dG(x)$ and $\lambda>0$, the full conclusion is
--
--   $$
--   1=\bar P_0\ge\bar P_1\ge\cdots\ge0,\qquad
--   \bar P_k/\bar P_{k-1}\text{ decreases for }k\ge1,\qquad
--   \bar H\text{ is IHR}.
--   $$
--
--   The mixture $\bar H$ is exactly (5.2). No density is required for the damage law: PF₂ applies to its CDF. The three conclusions state normalization and monotonicity, the successive-ratio condition, and continuous-time increasing hazard rate.
--
--   **Formalization Note** The source states $F$ is PF₂ and $g$ is PF₂; we use their real difference kernels. Probability support and $G(0)=0$ are measure hypotheses, and $g$ is a chosen nonnegative Lebesgue-measurable density inducing $G$. The ratio condition is the published cross-product predicate, reindexed from $k\ge1$ to adjacent indices starting at zero. The IHR predicate concerns nonnegative ages. The threshold density ensures no common discontinuities with convolution CDFs.
--
--   Differences from the source:
--   - encoding: nonnegative damage distribution F and threshold distribution G with G(0)=0 → probability measures μ,ν on ℝ with μ(−∞,0)=0 and ν(−∞,0]=0; reason: CDFs are masses of closed lower intervals; all atoms and nonnegative damage laws are represented
--   - encoding: a chosen PF₂ density version → a nonnegative Lebesgue-measurable density inducing the law and a TP₂ difference kernel; reason: this is Definition 2.3 applied to the chosen version; no moment, smoothness or strict-positivity condition is added
--   - encoding: F is a PF₂ distribution function → the actual CDF x↦μ(−∞,x] has a TP₂ difference kernel; reason: this does not require a damage density and does not replace the CDF with survival
--   - encoding: successive ratios on their nonzero-denominator domain → all ordered cross-product inequalities on the nonnegative sequence; reason: this is the zero-compatible log-convex or PF₂ ratio convention; no division-by-zero value is used, and no inference from adjacent ratios across gaps is assumed
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 646, Theorem 5.5; https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_RandThreshold_Model
import Definitions.Def_ShockWear_Inherit_Supplement_TotalPositivity
import Definitions.Def_ShockWear_Inherit_Supplement_Density

namespace ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem55 (lam : ℝ) (hlam : 0 < lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iic 0) = 0)
    (hF : IsPF2Function (fun x => (μ (Set.Iic x)).toReal))
    (g : ℝ → ℝ) (hg : IsDensity ν g) (hpg : IsPF2Function g) :
    ShockWear.RandThreshold.randP μ ν 0 = 1 ∧
    Antitone (ShockWear.RandThreshold.randP μ ν) ∧
    (∀ k, 0 ≤ ShockWear.RandThreshold.randP μ ν k) ∧
    IsPF2SeqFrom 0 (ShockWear.RandThreshold.randP μ ν) ∧
    IsIHR (ShockWear.RandThreshold.shockSurv lam (ShockWear.RandThreshold.randP μ ν)) := by sorry

end ShockWear.Inherit.Supplement
