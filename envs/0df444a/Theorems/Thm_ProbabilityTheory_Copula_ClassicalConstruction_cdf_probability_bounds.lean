-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_ClassicalConstruction_cdf_probability_bounds
-- name    : ProbabilityTheory.Copula.ClassicalConstruction.cdf_probability_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:54:53.953685+00:00
-- url     : https://prove2.me/theorems/ea3dcb19-6873-455d-b5e9-7981ce03c973
-- title:
--   Classical Construction: cdf probability bounds
-- statement:
--   The Classical Construction construction uses the cdf probability bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Approximation.lean#L208-L252
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Approximation.lean#L208-L252

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

theorem ProbabilityTheory.Copula.ClassicalConstruction.cdf_probability_bounds (hF : IsClassical F)
    (D : Division (fun _ : Fin d => 0) (fun _ => 1)) {ε : ℝ} (hε : 0 ≤ ε)
    (hmesh : D.All (fun a b => ∀ i, (b i : ℝ) - (a i : ℝ) ≤ ε)) (u : Fin d → I) :
    F u - (d : ℝ) * ε ≤ (probability hF D).toMeasure.real (Iic u) ∧
      (probability hF D).toMeasure.real (Iic u) ≤ F u := by sorry
