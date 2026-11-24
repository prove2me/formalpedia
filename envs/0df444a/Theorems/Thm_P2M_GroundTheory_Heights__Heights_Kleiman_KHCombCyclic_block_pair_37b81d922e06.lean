-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_block_pair_37b81d922e06
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_block_pair_37b81d922e06
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:32.672807+00:00
-- url     : https://prove2.me/theorems/c391bd30-f71a-4709-9bb2-88a91ea41f75
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic block pair 37b81d922e06: P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic block pair 37b81d922e06
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic block pair 37b81d922e06 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic block pair 37b81d922e06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L93-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L93-L120

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_block_pair_37b81d922e06 (J : ∀ k, Finset (ι k)) (n : ℕ) (f : CombC S J n) (I : CombCell ι J (n + 1)) (k : K)
    (hJ : J k = ∅) (h2 : (I.1.1 k).card = 2)
    (hf : ∀ i ∈ I.1.1 k, ∀ j ∈ I.1.1 k,
      ∀ (hi : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)))
        (hj : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase j))),
      f ⟨⟨_, hi.1⟩, hi.2⟩ = f ⟨⟨_, hj.1⟩, hj.2⟩) :
    ∑ i ∈ I.1.1 k, (if h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)) then
        (KH.faceSign I.1.1 k i : ℤ) • f ⟨⟨_, h.1⟩, h.2⟩ else 0) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombCyclic».«block_pair» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_block_pair_37b81d922e06
