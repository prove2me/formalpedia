-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_combD_apply_6bfad6589386
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_combD_apply_6bfad6589386
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:19.941946+00:00
-- url     : https://prove2.me/theorems/43a12117-ab7e-460e-9409-bd6da0cd9f01
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic comb D apply 6bfad6589386: P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic comb D apply 6bfad6589386
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic comb D apply 6bfad6589386 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic comb D apply 6bfad6589386 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L22-L31

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_combD_apply_6bfad6589386 (J : ∀ k, Finset (ι k)) (n : ℕ) (f : CombC S J n) (I : CombCell ι J (n + 1)) :
    combD S J n f I = ∑ k, ∑ i ∈ I.1.1 k,
      if h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)) then
        (KH.faceSign I.1.1 k i : ℤ) • f ⟨⟨Function.update I.1.1 k ((I.1.1 k).erase i), h.1⟩, h.2⟩
      else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombCyclic».«combD_apply» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_combD_apply_6bfad6589386
