-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_of_empty_fe169bb191f2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_of_empty_fe169bb191f2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:32.867182+00:00
-- url     : https://prove2.me/theorems/44705dc2-7589-4fb7-972e-86bf904c5650
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext of empty fe169bb191f2: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext of empty fe169bb191f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext of empty fe169bb191f2 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext of empty fe169bb191f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L215-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L215-L222

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_of_empty_fe169bb191f2 (J : ∀ k, Finset (ι k)) (n : ℕ) (φ : CombC S J n) (T : ∀ k, Finset (ι k))
    (hT : ∃ l, T l = ∅) : ext J n φ T = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«ext_of_empty» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_of_empty_fe169bb191f2
