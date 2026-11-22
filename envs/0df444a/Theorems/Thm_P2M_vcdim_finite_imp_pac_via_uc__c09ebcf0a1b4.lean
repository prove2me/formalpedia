-- Prove2me | Theorems.Thm_P2M_vcdim_finite_imp_pac_via_uc__c09ebcf0a1b4
-- name    : P2M_vcdim_finite_imp_pac_via_uc__c09ebcf0a1b4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:38.67764+00:00
-- url     : https://prove2.me/theorems/dd976dd7-12b2-488c-87dd-dca08c20ff3d
-- title:
--   P2 M vcdim finite imp pac via uc  c09ebcf0a1b4: P2 M vcdim finite imp pac via uc  c09ebcf0a1b4
-- statement:
--   VCDim < ⊤ → PACLearnable via UC route.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1961-L1970
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1961-L1970

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal

theorem P2M_vcdim_finite_imp_pac_via_uc__c09ebcf0a1b4 (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hC : VCDim X C < ⊤)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    PACLearnable X C := by sorry

alias «vcdim_finite_imp_pac_via_uc'» := P2M_vcdim_finite_imp_pac_via_uc__c09ebcf0a1b4
