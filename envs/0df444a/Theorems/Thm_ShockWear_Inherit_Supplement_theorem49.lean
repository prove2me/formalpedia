-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem49
-- name    : ShockWear.Inherit.Supplement.theorem49
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T23:55:22.08612+00:00
-- url     : https://prove2.me/theorems/803ce131-c8c9-46c5-a79f-f96b28101c91
-- title:
--   Theorem 4.9 — All three implications in the convolution PF₂–TP₂–IHR chain
-- statement:
--   Let $F$ be a probability law supported on $[0,\infty)$, $F^{(0)}=\delta_0$, and $\lambda>0$. The following three implications hold separately under their immediate antecedents:
--
--   $$
--   F\text{ is PF}_2\Longrightarrow (k,x)\mapsto F^{(k)}(x)\text{ is TP}_2,
--   $$
--   $$
--   (k,x)\mapsto F^{(k)}(x)\text{ is TP}_2\Longrightarrow
--   \text{for every }x,\ (F^{(k)}(x))_{k\ge0}\text{ is PF}_2,
--   $$
--   $$
--   \text{for each }x,\ (F^{(k)}(x))_{k\ge0}\text{ is PF}_2
--   \Longrightarrow \bar H_x\text{ is IHR}.
--   $$
--
--   Here $F$ in the first premise is the CDF, not its survival function or a density; $\bar H_x$ is the Poisson mixture (4.7). The TP₂ kernel orders $k$ and $x$ in the same increasing direction. The last implication is pointwise in $x$ and does not assume either previous antecedent.
--
--   **Formalization Note** The source states PF₂ and TP₂; we use their full order-one and order-two determinant definitions. Discrete PF₂ uses the sequence extended by zero to negative integer indices, with the difference kernel, not a Hankel kernel. All nonnegative convolution indices and all real thresholds are included.
--
--   Differences from the source:
--   - encoding: nonnegative distribution F, convolution CDFs, and Poisson mixture → a supported probability measure, the published cdfPow and shockSurv, λ>0; reason: the statement retains the actual CDF, not a free object constrained by a desired property
--   - encoding: PF₂ functions/sequences and TP₂ in k,x → full TP₂ difference kernels on ℝ or ℤ, zero extension at negative sequence indices; reason: Definition 2.3 includes order one; the integer difference kernel preserves support and all minors
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 640, Theorem 4.9; https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_Inherit_Supplement_TotalPositivity

namespace ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem49 (lam : ℝ) (hlam : 0 < lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) :
    (IsPF2Function (fun x => (μ (Set.Iic x)).toReal) →
      IsTP 2 Set.univ Set.univ (fun k x => ShockWear.CumDamage.cdfPow μ k x)) ∧
    (IsTP 2 Set.univ Set.univ (fun k x => ShockWear.CumDamage.cdfPow μ k x) →
      ∀ x : ℝ, IsPF2Sequence (fun k => ShockWear.CumDamage.cdfPow μ k x)) ∧
    (∀ x : ℝ, IsPF2Sequence (fun k => ShockWear.CumDamage.cdfPow μ k x) →
      IsIHR (ShockWear.CumDamage.shockSurv lam (fun k => ShockWear.CumDamage.cdfPow μ k x))) := by sorry

end ShockWear.Inherit.Supplement
