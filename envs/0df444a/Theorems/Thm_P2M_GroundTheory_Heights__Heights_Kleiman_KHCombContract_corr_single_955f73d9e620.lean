-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_corr_single_955f73d9e620
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_corr_single_955f73d9e620
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:24.063341+00:00
-- url     : https://prove2.me/theorems/b1609bd1-230b-4415-8547-d708a1560590
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract corr single 955f73d9e620: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract corr single 955f73d9e620
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract corr single 955f73d9e620 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract corr single 955f73d9e620 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L371-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L371-L397

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_corr_single_955f73d9e620 (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (d : ℕ) (φ : CombC S J d) (I : CombCell ι J d)
    (hJk : J k = ∅) (h1 : (I.1.1 k).card = 1) :
    tD (corr J k i₀ d φ) I.1.1 = φ (repl J k i₀ d I hJk h1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«corr_single» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_corr_single_955f73d9e620
