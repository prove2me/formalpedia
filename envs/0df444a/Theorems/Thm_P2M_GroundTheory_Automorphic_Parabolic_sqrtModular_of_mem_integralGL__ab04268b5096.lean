-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_Parabolic_sqrtModular_of_mem_integralGL__ab04268b5096
-- name    : P2M_GroundTheory_Automorphic_Parabolic_sqrtModular_of_mem_integralGL__ab04268b5096
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:48:07.668887+00:00
-- url     : https://prove2.me/theorems/fc4f72d8-c098-45aa-ae42-8dfb7532aeca
-- title:
--   P2 M Ground Theory Automorphic Parabolic sqrt Modular of mem integral GL  ab04268b5096: P2 M Ground Theory Automorphic Parabolic sqrt Modular of mem integral GL  ab04268b5096
-- statement:
--   The P2 M Ground Theory Automorphic Parabolic sqrt Modular of mem integral GL  ab04268b5096 construction uses the P2 M Ground Theory Automorphic Parabolic sqrt Modular of mem integral GL  ab04268b5096 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L178-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L178-L182

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

theorem P2M_GroundTheory_Automorphic_Parabolic_sqrtModular_of_mem_integralGL__ab04268b5096 {p : blockUpper F n β}
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) : sqrtModular F n β p = 1 := by sorry

alias «GroundTheory».«Automorphic».«Parabolic».«sqrtModular_of_mem_integralGL'» := P2M_GroundTheory_Automorphic_Parabolic_sqrtModular_of_mem_integralGL__ab04268b5096
