-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsSklarCopula_unique
-- name    : ProbabilityTheory.Copula.IsSklarCopula.unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:44:34.014819+00:00
-- url     : https://prove2.me/theorems/01020d23-aaaf-4bc8-87a5-f92256aa2d6f
-- title:
--   Is Sklar Copula: unique
-- statement:
--   Continuous marginals make the Sklar copula unique on the entire unit cube.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Sklar/Continuous.lean#L122-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Sklar/Continuous.lean#L122-L130

module
public import Definitions.Def_LeanPool_Copula_Distribution_ProbabilityIntegralTransform
public import Definitions.Def_LeanPool_Copula_CDF_Continuity
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Sklar_Continuous
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.IsSklarCopula.unique {μ : ProbabilityMeasure (Fin d → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C D : Copula d}
    (hC : IsSklarCopula μ C) (hD : IsSklarCopula μ D) : C = D := by sorry
