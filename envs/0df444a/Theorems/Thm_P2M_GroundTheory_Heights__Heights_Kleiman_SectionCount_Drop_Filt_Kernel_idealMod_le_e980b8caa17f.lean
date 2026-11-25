-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_idealMod_le_e980b8caa17f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_idealMod_le_e980b8caa17f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:16.286302+00:00
-- url     : https://prove2.me/theorems/145cea9c-6cfd-5787-a2f9-14f70968f6be
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel ideal Mod le e980b8caa17f: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel ideal Mod le e980b8caa1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel ideal Mod le e980b8caa17f construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Filt Kernel ideal Mod le e980b8caa17f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropFiltKernel.lean#L35-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropFiltKernel.lean#L35-L83

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_idealMod_le_e980b8caa17f (j : Fin (N + 1)) (b : ℕ) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    idealMod (primeOf (S := S) x ⊔ zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b)) I ≤
      Submodule.span (chartRing S x I) {x j ^ b / x i ^ b} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Filt».«Kernel».«idealMod_le» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_idealMod_le_e980b8caa17f
