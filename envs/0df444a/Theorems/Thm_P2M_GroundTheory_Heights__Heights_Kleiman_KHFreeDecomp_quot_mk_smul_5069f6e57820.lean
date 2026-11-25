-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_quot_mk_smul_5069f6e57820
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_quot_mk_smul_5069f6e57820
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:14.774735+00:00
-- url     : https://prove2.me/theorems/731269c4-eebb-4f16-81db-00797c5ac292
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp quot mk smul 5069f6e57820: P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp quot mk smul 5069f6e57820
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp quot mk smul 5069f6e57820 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp quot mk smul 5069f6e57820 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeDecomp.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeDecomp.lean#L49-L51

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_quot_mk_smul_5069f6e57820 (s : S) (p : MRingOver S ι) :
    Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (s • p) = s • Ideal.Quotient.mk ⊥ p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHFreeDecomp».«quot_mk_smul» := P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_quot_mk_smul_5069f6e57820
