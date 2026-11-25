-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_homotopy_zero_79af76184472
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_homotopy_zero_79af76184472
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:40:54.762076+00:00
-- url     : https://prove2.me/theorems/1809ed83-6e87-59a3-b28e-af8df1315e5d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract homotopy zero 79af76184472: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract homotopy zero 79af76184472
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract homotopy zero 79af76184472 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract homotopy zero 79af76184472 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L438-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L438-L442

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_homotopy_zero_79af76184472 (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (φ : CombC S J 0) (I : CombCell ι J 0) :
    hh J k i₀ 0 (combD S J 0 φ) I + tD (corr J k i₀ 0 φ) I.1.1 = φ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«homotopy_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_homotopy_zero_79af76184472
