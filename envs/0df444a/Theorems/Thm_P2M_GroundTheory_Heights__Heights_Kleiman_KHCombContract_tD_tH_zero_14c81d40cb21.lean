-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_zero_14c81d40cb21
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_zero_14c81d40cb21
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:26:36.596574+00:00
-- url     : https://prove2.me/theorems/43ab6b07-d4b9-4c16-b3fd-9044803365ce
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D t H zero 14c81d40cb21: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D t H zero 14c81d40cb21
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D t H zero 14c81d40cb21 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D t H zero 14c81d40cb21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L330-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L330-L348

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_zero_14c81d40cb21 (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (φ : CombC S J 0) (I : CombCell ι J 0) :
    tD (tH k i₀ (ext J 0 φ)) I.1.1 = tD (corr J k i₀ 0 φ) I.1.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«tD_tH_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_zero_14c81d40cb21
