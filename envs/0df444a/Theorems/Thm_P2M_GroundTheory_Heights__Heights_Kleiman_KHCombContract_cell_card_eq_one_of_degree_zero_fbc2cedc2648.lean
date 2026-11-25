-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_cell_card_eq_one_of_degree_zero_fbc2cedc2648
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_cell_card_eq_one_of_degree_zero_fbc2cedc2648
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:38.54042+00:00
-- url     : https://prove2.me/theorems/2b7f6640-aa5d-4cfb-acee-42a77287eb56
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract cell card eq one of degree zero fbc2cedc2648: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract cell card eq one of degree zero fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract cell card eq one of degree zero fbc2cedc2648 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract cell card eq one of degree zero fbc2cedc2648 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L323-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L323-L328

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_cell_card_eq_one_of_degree_zero_fbc2cedc2648 (I : KH.Cell K ι 0) (l : K) : (I.1 l).card = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«cell_card_eq_one_of_degree_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_cell_card_eq_one_of_degree_zero_fbc2cedc2648
