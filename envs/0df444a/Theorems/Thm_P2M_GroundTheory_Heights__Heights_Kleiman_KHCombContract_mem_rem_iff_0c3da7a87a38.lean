-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_mem_rem_iff_0c3da7a87a38
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_mem_rem_iff_0c3da7a87a38
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:37.303688+00:00
-- url     : https://prove2.me/theorems/f1a96ca5-f6a4-47da-85b1-0c763ca83819
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract mem rem iff 0c3da7a87a38: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract mem rem iff 0c3da7a87a38
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract mem rem iff 0c3da7a87a38 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract mem rem iff 0c3da7a87a38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L150-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L150-L157

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_mem_rem_iff_0c3da7a87a38 (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (l : K) (i : ι l) :
    i₀ ∈ rem T l i k ↔ i₀ ∈ T k ∧ (⟨l, i⟩ : Σ k, ι k) ≠ ⟨k, i₀⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«mem_rem_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_mem_rem_iff_0c3da7a87a38
