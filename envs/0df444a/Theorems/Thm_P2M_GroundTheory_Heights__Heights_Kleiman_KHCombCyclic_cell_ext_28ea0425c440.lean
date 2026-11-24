-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_cell_ext_28ea0425c440
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_cell_ext_28ea0425c440
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:54.788259+00:00
-- url     : https://prove2.me/theorems/3ade2b96-72af-4d5b-8420-d17c9b2f6320
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic cell ext 28ea0425c440: P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic cell ext 28ea0425c440
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic cell ext 28ea0425c440 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic cell ext 28ea0425c440 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L33-L34

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_cell_ext_28ea0425c440 {J : ∀ k, Finset (ι k)} {n : ℕ} {I₁ I₂ : CombCell ι J n} (h : I₁.1.1 = I₂.1.1) : I₁ = I₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombCyclic».«cell_ext» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_cell_ext_28ea0425c440
