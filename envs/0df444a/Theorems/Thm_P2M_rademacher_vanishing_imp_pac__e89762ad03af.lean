-- Prove2me | Theorems.Thm_P2M_rademacher_vanishing_imp_pac__e89762ad03af
-- name    : P2M_rademacher_vanishing_imp_pac__e89762ad03af
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:39:46.668806+00:00
-- url     : https://prove2.me/theorems/54a1537b-a071-48b8-a92c-4d48d68581d4
-- title:
--   P2 M rademacher vanishing imp pac  e89762ad03af: P2 M rademacher vanishing imp pac  e89762ad03af
-- statement:
--   Typeclass version of rademacher_vanishing_imp_pac.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GeneralizationResults.lean#L286-L294
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GeneralizationResults.lean#L286-L294

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable

theorem P2M_rademacher_vanishing_imp_pac__e89762ad03af (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) [MeasurableConceptClass X C]
    (hrad : ∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D →
      ∀ m ≥ m₀, RademacherComplexity X C D m < ε) :
    PACLearnable X C := by sorry

alias «rademacher_vanishing_imp_pac'» := P2M_rademacher_vanishing_imp_pac__e89762ad03af
