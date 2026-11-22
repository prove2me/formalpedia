-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_ClassicalConstruction_Division_le_measure_Iic
-- name    : ProbabilityTheory.Copula.ClassicalConstruction.Division.le_measure_Iic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:54:48.198548+00:00
-- url     : https://prove2.me/theorems/93fed3fa-d30c-477a-b8d9-c65aad3a8abb
-- title:
--   Division: le measure Iic
-- statement:
--   The Division construction uses the le measure Iic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Approximation.lean#L121-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Approximation.lean#L121-L148

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

theorem ProbabilityTheory.Copula.ClassicalConstruction.Division.le_measure_Iic (hF : IsClassical F) (D : Division a b) {ε : ℝ}
    (hmesh : D.All (fun a b => ∀ i, (b i : ℝ) - (a i : ℝ) ≤ ε))
    (u w : Fin d → I) (hw : ∀ i, w i = 0 ∨ (w i : ℝ) + ε ≤ (u i : ℝ)) :
    ENNReal.ofReal (rectangleIncrement F (a ⊓ w) (b ⊓ w)) ≤ D.measure F (Iic u) := by sorry
