-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_toMeasure_comonotonic
-- name    : ProbabilityTheory.Copula.toMeasure_comonotonic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:46.153432+00:00
-- url     : https://prove2.me/theorems/2a682402-e5c4-4dc8-a1e7-e94b5b7f5b7d
-- title:
--   Copula: to Measure comonotonic
-- statement:
--   The Copula construction uses the to Measure comonotonic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Comonotonic.lean#L31-L33
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Comonotonic.lean#L31-L33

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Comonotonic
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula

theorem ProbabilityTheory.Copula.toMeasure_comonotonic (d : ℕ) :
    (comonotonic d).toMeasure =
      (volume : Measure I).map (fun u (_ : Fin d) => u) := by sorry

attribute [defeq] ProbabilityTheory.Copula.toMeasure_comonotonic
