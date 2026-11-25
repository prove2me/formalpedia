-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sigma_ins_74b9079c2014
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sigma_ins_74b9079c2014
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:26:00.498799+00:00
-- url     : https://prove2.me/theorems/373baf9b-3a93-4d9b-b8f4-15879544a14b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sigma ins 74b9079c2014: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sigma ins 74b9079c2014
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sigma ins 74b9079c2014 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sigma ins 74b9079c2014 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L124-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L124-L130

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sigma_ins_74b9079c2014 (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) :
    Finset.univ.sigma (ins k i₀ T) = insert ⟨k, i₀⟩ (Finset.univ.sigma T) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«sigma_ins» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sigma_ins_74b9079c2014
