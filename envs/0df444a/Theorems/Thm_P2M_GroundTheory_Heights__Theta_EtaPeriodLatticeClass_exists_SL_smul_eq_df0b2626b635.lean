-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_exists_SL_smul_eq_df0b2626b635
-- name    : P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_exists_SL_smul_eq_df0b2626b635
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:26.625852+00:00
-- url     : https://prove2.me/theorems/569cfcb1-410e-42d2-bdab-3775daf69718
-- title:
--   P2 M Ground Theory Heights  Theta Eta Period Lattice Class exists SL smul eq df0b2626b635: P2 M Ground Theory Heights  Theta Eta Period Lattice Class exists SL smul eq df0b2626b635
-- statement:
--   The P2 M Ground Theory Heights  Theta Eta Period Lattice Class exists SL smul eq df0b2626b635 construction uses the P2 M Ground Theory Heights  Theta Eta Period Lattice Class exists SL smul eq df0b2626b635 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmEtaPeriodLatticeClassPf.lean#L61-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmEtaPeriodLatticeClassPf.lean#L61-L111

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup ModularForm Complex
open scoped Real Modular MatrixGroups
open GroundTheory.Heights₂.Theta.EtaPeriodLatticeClass

theorem P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_exists_SL_smul_eq_df0b2626b635 {τ τ' : ℍ} {μ : ℂ} (hμ : μ ≠ 0)
    (h1 : ∀ z ∈ latticeOf (τ : ℂ), μ * z ∈ latticeOf (τ' : ℂ))
    (h2 : ∀ w ∈ latticeOf (τ' : ℂ), μ⁻¹ * w ∈ latticeOf (τ : ℂ)) :
    ∃ γ : SL(2, ℤ), γ • τ = τ' := by sorry

alias «GroundTheory».«Heights₂».«Theta».«EtaPeriodLatticeClass».«exists_SL_smul_eq» := P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_exists_SL_smul_eq_df0b2626b635
