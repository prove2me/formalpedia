-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_succ_1890396c1f6c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_succ_1890396c1f6c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:32:20.677917+00:00
-- url     : https://prove2.me/theorems/4fbb50a6-1716-50be-9695-d71ff082e322
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D t H succ 1890396c1f6c: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D t H succ 1890396c1f6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D t H succ 1890396c1f6c construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D t H succ 1890396c1f6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L311-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L311-L321

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_succ_1890396c1f6c (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (hJ0 : i₀ ∉ J k) (m : ℕ) (φ : CombC S J (m + 1))
    (I : CombCell ι J (m + 1)) :
    tD (tH k i₀ (ext J (m + 1) φ)) I.1.1 =
      combD S J m (hh J k i₀ m φ) I + tD (corr J k i₀ (m + 1) φ) I.1.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«tD_tH_succ» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_succ_1890396c1f6c
