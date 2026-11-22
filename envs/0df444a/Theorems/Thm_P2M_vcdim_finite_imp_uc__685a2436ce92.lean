-- Prove2me | Theorems.Thm_P2M_vcdim_finite_imp_uc__685a2436ce92
-- name    : P2M_vcdim_finite_imp_uc__685a2436ce92
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:36.899803+00:00
-- url     : https://prove2.me/theorems/180c7628-f1d0-4402-8e86-605b398bff72
-- title:
--   P2 M vcdim finite imp uc  685a2436ce92: P2 M vcdim finite imp uc  685a2436ce92
-- statement:
--   The P2 M vcdim finite imp uc  685a2436ce92 construction uses the P2 M vcdim finite imp uc  685a2436ce92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1771-L1958
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1771-L1958

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

theorem P2M_vcdim_finite_imp_uc__685a2436ce92 (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hC : VCDim X C < ⊤)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    HasUniformConvergence X C := by sorry

alias «vcdim_finite_imp_uc'» := P2M_vcdim_finite_imp_uc__685a2436ce92
