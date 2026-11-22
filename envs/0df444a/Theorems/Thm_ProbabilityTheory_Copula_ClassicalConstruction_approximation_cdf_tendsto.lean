-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_ClassicalConstruction_approximation_cdf_tendsto
-- name    : ProbabilityTheory.Copula.ClassicalConstruction.approximation_cdf_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:54:50.672997+00:00
-- url     : https://prove2.me/theorems/ae106737-0539-4205-9c7b-2609f7b7e455
-- title:
--   Classical Construction: approximation cdf tendsto
-- statement:
--   CDFs of the finite atomic approximations converge to the classical function.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Approximation.lean#L272-L281
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Approximation.lean#L272-L281

module
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Approximation
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval ENNReal BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
open ProbabilityTheory.Copula.ClassicalConstruction

theorem ProbabilityTheory.Copula.ClassicalConstruction.approximation_cdf_tendsto (hF : IsClassical F) (u : Fin d → I) :
    Filter.Tendsto (fun n => (approximation hF n).toMeasure.real (Iic u)) Filter.atTop
      (nhds (F u)) := by sorry
