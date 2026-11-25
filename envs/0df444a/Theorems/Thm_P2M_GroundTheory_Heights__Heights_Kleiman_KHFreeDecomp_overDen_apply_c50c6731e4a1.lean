-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_overDen_apply_c50c6731e4a1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_overDen_apply_c50c6731e4a1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:00.979718+00:00
-- url     : https://prove2.me/theorems/13f050ac-5241-441d-9304-8c851fbc543d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp over Den apply c50c6731e4a1: P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp over Den apply c50c6731e4a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp over Den apply c50c6731e4a1 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp over Den apply c50c6731e4a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeDecomp.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeDecomp.lean#L44-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeDecompSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHFreeDecomp
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_overDen_apply_c50c6731e4a1 (T : Submonoid (MRingOver S ι)) (t : T) (m : M) :
    overDen T t m = LocalizedModule.mk m t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHFreeDecomp».«overDen_apply» := P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_overDen_apply_c50c6731e4a1
