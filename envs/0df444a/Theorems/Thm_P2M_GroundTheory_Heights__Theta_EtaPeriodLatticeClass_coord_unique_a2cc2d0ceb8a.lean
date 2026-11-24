-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_coord_unique_a2cc2d0ceb8a
-- name    : P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_coord_unique_a2cc2d0ceb8a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:48.763898+00:00
-- url     : https://prove2.me/theorems/9f8c3d71-0664-4e78-97cd-02a6ece016ee
-- title:
--   P2 M Ground Theory Heights  Theta Eta Period Lattice Class coord unique a2cc2d0ceb8a: P2 M Ground Theory Heights  Theta Eta Period Lattice Class coord unique a2cc2d0ceb8a
-- statement:
--   The P2 M Ground Theory Heights  Theta Eta Period Lattice Class coord unique a2cc2d0ceb8a construction uses the P2 M Ground Theory Heights  Theta Eta Period Lattice Class coord unique a2cc2d0ceb8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmEtaPeriodLatticeClassPf.lean#L48-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmEtaPeriodLatticeClassPf.lean#L48-L59

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

theorem P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_coord_unique_a2cc2d0ceb8a {τ : ℍ} {m n m' n' : ℤ}
    (h : (m : ℂ) + n * (τ : ℂ) = m' + n' * (τ : ℂ)) : m = m' ∧ n = n' := by sorry

alias «GroundTheory».«Heights₂».«Theta».«EtaPeriodLatticeClass».«coord_unique» := P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_coord_unique_a2cc2d0ceb8a
