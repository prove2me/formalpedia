-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_cdf_ofClassical
-- name    : ProbabilityTheory.Copula.cdf_ofClassical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T19:00:26.028722+00:00
-- url     : https://prove2.me/theorems/46cd8425-f16f-48ff-bb3f-aab93ae6694b
-- title:
--   Copula: cdf of Classical
-- statement:
--   The Copula construction uses the cdf of Classical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Characterization.lean#L114-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Characterization.lean#L114-L115

module
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Definitions.Def_LeanPool_Copula_Classical_Approximation
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_Classical_Characterization
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval Topology ENNReal BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}

theorem ProbabilityTheory.Copula.cdf_ofClassical (F : (Fin d → I) → ℝ) (hF : IsClassical F) :
    (ofClassical F hF).cdf = F := by sorry
