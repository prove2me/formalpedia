-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_cyclic_cohom_2409c2a8089e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_cyclic_cohom_2409c2a8089e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:32:28.188929+00:00
-- url     : https://prove2.me/theorems/1b381400-f5ad-5950-9d7d-b7f85dfd5b18
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic cyclic cohom 2409c2a8089e: P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic cyclic cohom 2409c2a8089e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic cyclic cohom 2409c2a8089e construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic cyclic cohom 2409c2a8089e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L243-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L243-L329

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombCyclicSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombCyclic
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
open GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_cyclic_cohom_2409c2a8089e (hC : KHCombContract.Statement) (J : ∀ k, Finset (ι k)) (n : ℕ)
    (hJ : ∀ k, J k = ∅ ∨ J k = Finset.univ) (f : CombC S J n) (hf : combD S J n f = 0) :
    ∃ s : S, f - s • singOne S J n ∈ combB S J n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombCyclic».«cyclic_cohom» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_cyclic_cohom_2409c2a8089e
