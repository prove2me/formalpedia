-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_exists_sklarCopula_unit
-- name    : ProbabilityTheory.Copula.exists_sklarCopula_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:08.417396+00:00
-- url     : https://prove2.me/theorems/c492b640-8df0-4a49-b327-b4f8e171260b
-- title:
--   Copula: exists sklar Copula unit
-- statement:
--   Every joint law on the unit cube has a Sklar copula, including laws with atoms.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Sklar/UnitInterval.lean#L32-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Sklar/UnitInterval.lean#L32-L48

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Distribution_Quantile
public import Definitions.Def_LeanPool_Copula_Sklar_Lift
public import Definitions.Def_LeanPool_Copula_Sklar_UnitInterval
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.exists_sklarCopula_unit (μ : ProbabilityMeasure (Fin d → I)) :
    ∃ C : Copula d, ∀ x : Fin d → I,
      C.cdf (fun i => unitMarginalCDF μ i (x i)) = μ.toMeasure.real (Iic x) := by sorry
