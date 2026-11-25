-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_hh_5b992995b6b6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_hh_5b992995b6b6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:41.104603+00:00
-- url     : https://prove2.me/theorems/64cea227-9f2c-4ce9-8bdb-13fd6b95dad5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext hh 5b992995b6b6: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext hh 5b992995b6b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext hh 5b992995b6b6 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext hh 5b992995b6b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L289-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L289-L297

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_hh_5b992995b6b6 (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (hJ0 : i₀ ∉ J k) (m : ℕ) (φ : CombC S J (m + 1))
    (T : ∀ k, Finset (ι k)) (hk : (T k).Nonempty) :
    ext J m (hh J k i₀ m φ) T = tH k i₀ (ext J (m + 1) φ) T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«ext_hh» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_hh_5b992995b6b6
