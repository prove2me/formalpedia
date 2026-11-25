-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_cond_ins_9efaac490a1c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_cond_ins_9efaac490a1c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:58.690558+00:00
-- url     : https://prove2.me/theorems/53826545-a7c0-43f6-ab83-a6c418cb4493
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract cond ins 9efaac490a1c: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract cond ins 9efaac490a1c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract cond ins 9efaac490a1c construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract cond ins 9efaac490a1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L245-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L245-L259

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_cond_ins_9efaac490a1c (J : ∀ k, Finset (ι k)) (d : ℕ) (k : K) (i₀ : ι k) (T : ∀ k, Finset (ι k)) (h0 : i₀ ∉ T k)
    (h : ((∀ l, (T l).Nonempty) ∧ ∑ l, ((T l).card - 1) = d) ∧ ∀ l, J l ⊆ T l) :
    ((∀ l, (ins k i₀ T l).Nonempty) ∧ ∑ l, ((ins k i₀ T l).card - 1) = d + 1) ∧ ∀ l, J l ⊆ ins k i₀ T l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«cond_ins» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_cond_ins_9efaac490a1c
