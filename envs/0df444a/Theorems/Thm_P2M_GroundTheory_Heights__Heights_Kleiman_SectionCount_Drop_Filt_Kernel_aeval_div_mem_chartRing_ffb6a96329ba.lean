-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_aeval_div_mem_chartRing_ffb6a96329ba
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_aeval_div_mem_chartRing_ffb6a96329ba
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:22.606436+00:00
-- url     : https://prove2.me/theorems/2c31ac99-d056-54dd-a532-9ff014bbd307
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel aeval div mem chart Ring ffb6a96329ba: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel aeval div m
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel aeval div mem chart Ring ffb6a96329ba construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel aeval div mem chart Ring ffb6a96329ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropFiltKernel.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropFiltKernel.lean#L27-L33

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_aeval_div_mem_chartRing_ffb6a96329ba (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (f : Poly S N) :
    aeval (fun l => x l / x i) f ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Filt».«Kernel».«aeval_div_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_aeval_div_mem_chartRing_ffb6a96329ba
