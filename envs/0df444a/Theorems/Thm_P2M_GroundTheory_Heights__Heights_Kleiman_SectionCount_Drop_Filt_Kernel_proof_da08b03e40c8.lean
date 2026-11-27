-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_proof_da08b03e40c8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_proof_da08b03e40c8
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:28:04.201552+00:00
-- url     : https://prove2.me/theorems/5c2b3244-0b67-5a3b-b6f1-d9015ce4d35d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel proof da08b03e40c8: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel proof da08b03e40c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel proof da08b03e40c8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel proof da08b03e40c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropFiltKernel.lean#L85-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropFiltKernel.lean#L85-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltKernelSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropFiltKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Kernel
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_proof_da08b03e40c8 : SectionCount.Drop.Filt.Kernel.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Filt».«Kernel».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_proof_da08b03e40c8
