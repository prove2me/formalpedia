-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_ClassicalConstruction_Division_measure_Iic_le
-- name    : ProbabilityTheory.Copula.ClassicalConstruction.Division.measure_Iic_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:54:53.856974+00:00
-- url     : https://prove2.me/theorems/a9f033d6-fa8b-48ea-9a77-1a435d480c60
-- title:
--   Division: measure Iic le
-- statement:
--   The Division construction uses the measure Iic le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Approximation.lean#L105-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Approximation.lean#L105-L119

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
open ProbabilityTheory.Copula.ClassicalConstruction.Division
variable {a b : Fin d → I}

theorem ProbabilityTheory.Copula.ClassicalConstruction.Division.measure_Iic_le (hF : IsClassical F) (D : Division a b) (u : Fin d → I) :
    D.measure F (Iic u) ≤ ENNReal.ofReal (rectangleIncrement F (a ⊓ u) (b ⊓ u)) := by sorry
