-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_lt_fe63e90e9641
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_lt_fe63e90e9641
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:28:21.335825+00:00
-- url     : https://prove2.me/theorems/c82189cd-7c42-4718-a603-5501dbc4fbbf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sign lt fe63e90e9641: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sign lt fe63e90e9641
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sign lt fe63e90e9641 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sign lt fe63e90e9641 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L44-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L44-L60

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_lt_fe63e90e9641 (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (l : K) (i : ι l) (hlk : l < k)
    (hi : i ∈ T l) (hcard : 2 ≤ (T l).card) :
    KH.faceSign (ins k i₀ (rem T l i)) k i₀ = - KH.faceSign (ins k i₀ T) k i₀ ∧
      KH.faceSign (ins k i₀ T) l i = KH.faceSign T l i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«sign_lt» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_lt_fe63e90e9641
