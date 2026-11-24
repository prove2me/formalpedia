-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_hh_combD_82ed48b4744a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_hh_combD_82ed48b4744a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:04.112946+00:00
-- url     : https://prove2.me/theorems/2f3b3d84-85f8-4140-8a42-a95bf11b38bb
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract hh comb D 82ed48b4744a: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract hh comb D 82ed48b4744a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract hh comb D 82ed48b4744a construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract hh comb D 82ed48b4744a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L299-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L299-L306

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_hh_combD_82ed48b4744a (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (m : ℕ) (φ : CombC S J m) (I : CombCell ι J m) :
    hh J k i₀ m (combD S J m φ) I = tH k i₀ (tD (ext J m φ)) I.1.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«hh_combD» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_hh_combD_82ed48b4744a
