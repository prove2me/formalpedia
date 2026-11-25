-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_contract_cocycle_0f3cdad47278
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_contract_cocycle_0f3cdad47278
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:31:25.415292+00:00
-- url     : https://prove2.me/theorems/6bf12261-ba50-42f8-845f-b88d43104d29
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic contract cocycle 0f3cdad47278: P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic contract cocycle 0f3cdad47278
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic contract cocycle 0f3cdad47278 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic contract cocycle 0f3cdad47278 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L166-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L166-L241

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_contract_cocycle_0f3cdad47278 (J : ∀ k, Finset (ι k)) (n : ℕ) (k : K) (i₀ : ι k) (hJ : J k = ∅)
    (φ g : CombC S J n) (hφ : combD S J n φ = 0)
    (hg1 : ∀ I : CombCell ι J n, (I.1.1 k).card = 1 →
      ∃ I' : CombCell ι J n, I'.1.1 k = {i₀} ∧ (∀ l, l ≠ k → I'.1.1 l = I.1.1 l) ∧ g I = φ I')
    (hg0 : ∀ I : CombCell ι J n, (I.1.1 k).card ≠ 1 → g I = 0) :
    combD S J n g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombCyclic».«contract_cocycle» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_contract_cocycle_0f3cdad47278
