-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sum_card_update_of_notMem_8b37477be765
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sum_card_update_of_notMem_8b37477be765
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:49.442864+00:00
-- url     : https://prove2.me/theorems/e937c1fc-1cb1-4c4d-b8ed-89cd41174b41
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sum card update of not Mem 8b37477be765: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sum card update of not Mem 8b37477be765
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sum card update of not Mem 8b37477be765 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sum card update of not Mem 8b37477be765 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L31-L33

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sum_card_update_of_notMem_8b37477be765 (T : ∀ k, Finset (ι k)) (l : K) (A : Finset (ι l)) (s : Finset K) (hl : l ∉ s) :
    ∑ x ∈ s, ((Function.update T l A x).card - 1) = ∑ x ∈ s, ((T x).card - 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«sum_card_update_of_notMem» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sum_card_update_of_notMem_8b37477be765
