-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_zero_3c4d8f7b1f92
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_zero_3c4d8f7b1f92
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:27.548689+00:00
-- url     : https://prove2.me/theorems/30265866-f341-44d8-a372-bf85065b1ebf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext zero 3c4d8f7b1f92: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext zero 3c4d8f7b1f92
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext zero 3c4d8f7b1f92 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext zero 3c4d8f7b1f92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L229-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L229-L232

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_zero_3c4d8f7b1f92 (J : ∀ k, Finset (ι k)) (n : ℕ) : ext J n (0 : CombC S J n) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«ext_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_zero_3c4d8f7b1f92
