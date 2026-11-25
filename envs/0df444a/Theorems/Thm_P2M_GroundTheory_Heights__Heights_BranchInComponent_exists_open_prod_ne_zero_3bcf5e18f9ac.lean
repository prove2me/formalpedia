-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchInComponent_exists_open_prod_ne_zero_3bcf5e18f9ac
-- name    : P2M_GroundTheory_Heights__Heights_BranchInComponent_exists_open_prod_ne_zero_3bcf5e18f9ac
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:16:45.452213+00:00
-- url     : https://prove2.me/theorems/e64cb264-ca22-4daa-95ea-2ddb0197d002
-- title:
--   P2 M Ground Theory Heights  Heights Branch In Component exists open prod ne zero 3bcf5e18f9ac: P2 M Ground Theory Heights  Heights Branch In Component exists open prod ne zero 3bcf5e18f9ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Branch In Component exists open prod ne zero 3bcf5e18f9ac construction uses the P2 M Ground Theory Heights  Heights Branch In Component exists open prod ne zero 3bcf5e18f9ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchInComponent.lean#L21-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchInComponent.lean#L21-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchInComponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Metric Filter Topology Set
noncomputable section
open GroundTheory.Heights₂.Heights.BranchInComponent

theorem P2M_GroundTheory_Heights__Heights_BranchInComponent_exists_open_prod_ne_zero_3bcf5e18f9ac {k : ℕ} {U : Set (Fin k → ℂ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hne : U.Nonempty) {ι : Type*} (s : Finset ι) (f : ι → (Fin k → ℂ) → ℂ)
    (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) U) (hnz : ∀ i ∈ s, ¬ EqOn (f i) 0 U) :
    ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧ ∀ x ∈ V, ∏ i ∈ s, f i x ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BranchInComponent».«exists_open_prod_ne_zero» := P2M_GroundTheory_Heights__Heights_BranchInComponent_exists_open_prod_ne_zero_3bcf5e18f9ac
