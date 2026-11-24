-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_54fd778341b4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_54fd778341b4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:15:01.162429+00:00
-- url     : https://prove2.me/theorems/6af3653a-9630-4dc6-9719-26970529e3dd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D t H 54fd778341b4: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D t H 54fd778341b4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D t H 54fd778341b4 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract t D t H 54fd778341b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L159-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L159-L202

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_54fd778341b4 (k : K) (i₀ : ι k) (F : (∀ k, Finset (ι k)) → S) (hF : ∀ T, (∃ l, T l = ∅) → F T = 0)
    (T : ∀ k, Finset (ι k)) (hT : ∀ l, (T l).Nonempty) :
    tD (tH k i₀ F) T + tH k i₀ (tD F) T = F T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«tD_tH» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_tD_tH_54fd778341b4
