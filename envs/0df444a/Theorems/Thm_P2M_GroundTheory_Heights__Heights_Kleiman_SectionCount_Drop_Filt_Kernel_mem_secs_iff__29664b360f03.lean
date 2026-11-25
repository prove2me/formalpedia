-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_mem_secs_iff__29664b360f03
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_mem_secs_iff__29664b360f03
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:57:38.676427+00:00
-- url     : https://prove2.me/theorems/40287d00-ae96-5a1e-bcd1-e7fa90ae0769
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel mem secs iff  29664b360f03: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel mem secs iff  29664b36
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel mem secs iff  29664b360f03 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel mem secs iff  29664b360f03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropFiltKernel.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropFiltKernel.lean#L19-L20

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_mem_secs_iff__29664b360f03 {F : SubSystem S x Ω} {y : Ω} : y ∈ F.secs ↔ ∀ I, y ∈ F.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Filt».«Kernel».«mem_secs_iff'» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_mem_secs_iff__29664b360f03
