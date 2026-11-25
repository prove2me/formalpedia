-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_rem_ins_self_71e833acec92
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_rem_ins_self_71e833acec92
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:02.617571+00:00
-- url     : https://prove2.me/theorems/006af177-177d-4cc3-9fa5-6b4a82c338cf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract rem ins self 71e833acec92: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract rem ins self 71e833acec92
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract rem ins self 71e833acec92 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract rem ins self 71e833acec92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L132-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L132-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
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
open GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
variable {S : Type} [CommRing S]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_rem_ins_self_71e833acec92 (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (h : i₀ ∉ T k) :
    rem (ins k i₀ T) k i₀ = T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«rem_ins_self» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_rem_ins_self_71e833acec92
