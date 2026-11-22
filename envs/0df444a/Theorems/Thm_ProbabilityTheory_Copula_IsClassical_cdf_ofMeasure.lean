-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsClassical_cdf_ofMeasure
-- name    : ProbabilityTheory.Copula.IsClassical.cdf_ofMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:08.442109+00:00
-- url     : https://prove2.me/theorems/e1928545-cb8e-4c10-ac21-8c65eeb6864d
-- title:
--   Is Classical: cdf of Measure
-- statement:
--   The Is Classical construction uses the cdf of Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Basic.lean#L76-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Basic.lean#L76-L78

module
public import Definitions.Def_LeanPool_Copula_Rectangle
public import Definitions.Def_LeanPool_Copula_Unique
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_Classical_Basic
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.IsClassical.cdf_ofMeasure {F : (Fin d → I) → ℝ} (hF : IsClassical F)
    (μ : ProbabilityMeasure (Fin d → I)) (hμ : ∀ u, μ.toMeasure.real (Iic u) = F u) :
    (hF.ofMeasure μ hμ).cdf = F := by sorry
