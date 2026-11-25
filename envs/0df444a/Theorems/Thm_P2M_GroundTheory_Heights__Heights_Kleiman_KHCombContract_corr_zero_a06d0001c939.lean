-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_corr_zero_a06d0001c939
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_corr_zero_a06d0001c939
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:46.70418+00:00
-- url     : https://prove2.me/theorems/cab4ec0f-849b-4475-9cff-3460de00bd63
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract corr zero a06d0001c939: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract corr zero a06d0001c939
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract corr zero a06d0001c939 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract corr zero a06d0001c939 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L399-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L399-L428

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_corr_zero_a06d0001c939 (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (hJ0 : i₀ ∉ J k) (d : ℕ) (φ : CombC S J d)
    (I : CombCell ι J d) (h : ¬ (J k = ∅ ∧ (I.1.1 k).card = 1)) :
    tD (corr J k i₀ d φ) I.1.1 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«corr_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_corr_zero_a06d0001c939
