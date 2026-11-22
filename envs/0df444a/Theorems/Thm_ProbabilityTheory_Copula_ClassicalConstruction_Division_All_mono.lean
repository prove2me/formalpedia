-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_ClassicalConstruction_Division_All_mono
-- name    : ProbabilityTheory.Copula.ClassicalConstruction.Division.All.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:54:52.766355+00:00
-- url     : https://prove2.me/theorems/21b8053b-2038-47db-a970-d3341b2c9abd
-- title:
--   All: mono
-- statement:
--   The All construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Approximation.lean#L69-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Approximation.lean#L69-L73

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

theorem ProbabilityTheory.Copula.ClassicalConstruction.Division.All.mono {P Q : (Fin d → I) → (Fin d → I) → Prop} {D : Division a b}
    (h : D.All P) (hPQ : ∀ a b, P a b → Q a b) : D.All Q := by sorry
