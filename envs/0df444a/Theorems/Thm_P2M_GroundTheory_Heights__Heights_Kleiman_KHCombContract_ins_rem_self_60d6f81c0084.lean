-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ins_rem_self_60d6f81c0084
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ins_rem_self_60d6f81c0084
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:55.927513+00:00
-- url     : https://prove2.me/theorems/ddfdc903-1785-43b3-9e5b-1b367da3b4ed
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ins rem self 60d6f81c0084: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ins rem self 60d6f81c0084
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ins rem self 60d6f81c0084 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ins rem self 60d6f81c0084 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L136-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L136-L138

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ins_rem_self_60d6f81c0084 (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (h : i₀ ∈ T k) :
    ins k i₀ (rem T k i₀) = T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«ins_rem_self» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ins_rem_self_60d6f81c0084
