-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_isClassical_iff_existsUnique
-- name    : ProbabilityTheory.Copula.isClassical_iff_existsUnique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T19:00:30.593021+00:00
-- url     : https://prove2.me/theorems/4226331e-0426-45ff-bdb6-061435f8624b
-- title:
--   Copula: is Classical iff exists Unique
-- statement:
--   The Copula construction uses the is Classical iff exists Unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Characterization.lean#L122-L125
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Characterization.lean#L122-L125

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

theorem ProbabilityTheory.Copula.isClassical_iff_existsUnique : IsClassical F ↔ ∃! C : Copula d, C.cdf = F := by sorry
