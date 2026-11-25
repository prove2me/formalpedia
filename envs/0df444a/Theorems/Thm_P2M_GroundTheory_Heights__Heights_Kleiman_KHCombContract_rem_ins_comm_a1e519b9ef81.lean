-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_rem_ins_comm_a1e519b9ef81
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_rem_ins_comm_a1e519b9ef81
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:44.132422+00:00
-- url     : https://prove2.me/theorems/fa5f6196-8a78-483e-b268-3ae6047eba69
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract rem ins comm a1e519b9ef81: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract rem ins comm a1e519b9ef81
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract rem ins comm a1e519b9ef81 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract rem ins comm a1e519b9ef81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L140-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L140-L148

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_rem_ins_comm_a1e519b9ef81 (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (l : K) (i : ι l) (hi : i ∈ T l)
    (h0 : i₀ ∉ T k) : rem (ins k i₀ T) l i = ins k i₀ (rem T l i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«rem_ins_comm» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_rem_ins_comm_a1e519b9ef81
