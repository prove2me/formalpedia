-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_add_46340cde44a8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_add_46340cde44a8
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:39:28.788204+00:00
-- url     : https://prove2.me/theorems/2c0c4b11-beeb-54ee-9796-0225014c68a9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D add 46340cde44a8: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D add 46340cde44a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D add 46340cde44a8 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D add 46340cde44a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L120-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L120-L122

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_add_46340cde44a8 (F₁ F₂ : (∀ k, Finset (ι k)) → S) (T : ∀ k, Finset (ι k)) :
    tD (fun T' => F₁ T' + F₂ T') T = tD F₁ T + tD F₂ T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«tD_add» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_add_46340cde44a8
