-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_ofClassical_cdf
-- name    : ProbabilityTheory.Copula.ofClassical_cdf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T19:00:35.230356+00:00
-- url     : https://prove2.me/theorems/09713c1d-948e-4708-b552-d81c4783118f
-- title:
--   Copula: of Classical cdf
-- statement:
--   The Copula construction uses the of Classical cdf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Characterization.lean#L118-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Characterization.lean#L118-L120

module
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Definitions.Def_LeanPool_Copula_Classical_Approximation
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_Classical_Characterization
public import Theorems.Thm_ProbabilityTheory_Copula_isClassical_cdf

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval Topology ENNReal BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}

theorem ProbabilityTheory.Copula.ofClassical_cdf (C : Copula d) : ofClassical C.cdf C.isClassical_cdf = C := by sorry
