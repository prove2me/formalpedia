-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsSklarCopula_cdf_eq_on_ranges
-- name    : ProbabilityTheory.Copula.IsSklarCopula.cdf_eq_on_ranges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:44:36.951226+00:00
-- url     : https://prove2.me/theorems/214bd85e-8a06-4139-916c-45df4d9fce4a
-- title:
--   Is Sklar Copula: cdf eq on ranges
-- statement:
--   Factorizations agree on the product of marginal CDF ranges, even with atoms.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Sklar/Continuous.lean#L102-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Sklar/Continuous.lean#L102-L107

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

theorem ProbabilityTheory.Copula.IsSklarCopula.cdf_eq_on_ranges {μ : ProbabilityMeasure (Fin d → ℝ)} {C D : Copula d}
    (hC : IsSklarCopula μ C) (hD : IsSklarCopula μ D) (u : Fin d → I)
    (hu : ∀ i, u i ∈ Set.range (cdfUnit (marginal μ i))) : C.cdf u = D.cdf u := by sorry
