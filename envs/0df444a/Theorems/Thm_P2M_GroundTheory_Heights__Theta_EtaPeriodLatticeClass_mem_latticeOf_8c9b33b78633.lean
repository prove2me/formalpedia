-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_mem_latticeOf_8c9b33b78633
-- name    : P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_mem_latticeOf_8c9b33b78633
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:56.14356+00:00
-- url     : https://prove2.me/theorems/26f53371-54fe-4cae-b71f-f04b3e0dc84b
-- title:
--   P2 M Ground Theory Heights  Theta Eta Period Lattice Class mem lattice Of 8c9b33b78633: P2 M Ground Theory Heights  Theta Eta Period Lattice Class mem lattice Of 8c9b33b78633
-- statement:
--   The P2 M Ground Theory Heights  Theta Eta Period Lattice Class mem lattice Of 8c9b33b78633 construction uses the P2 M Ground Theory Heights  Theta Eta Period Lattice Class mem lattice Of 8c9b33b78633 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmEtaPeriodLatticeClassPf.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmEtaPeriodLatticeClassPf.lean#L39-L46

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

theorem P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_mem_latticeOf_8c9b33b78633 {τ z : ℂ} : z ∈ latticeOf τ ↔ ∃ m n : ℤ, z = m + n * τ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«EtaPeriodLatticeClass».«mem_latticeOf» := P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_mem_latticeOf_8c9b33b78633
