-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceOK_congr_1857042b9c83
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceOK_congr_1857042b9c83
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:03.282343+00:00
-- url     : https://prove2.me/theorems/d4daed79-2109-4d96-b6db-53de1b682879
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic face OK congr 1857042b9c83: P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic face OK congr 1857042b9c83
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic face OK congr 1857042b9c83 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Cyclic face OK congr 1857042b9c83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean#L36-L46

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceOK_congr_1857042b9c83 {J : ∀ k, Finset (ι k)} {n : ℕ} {k : K} (hJ : J k = ∅) {G G' : ∀ k, Finset (ι k)}
    (hc : (G k).card = (G' k).card) (ho : ∀ m, m ≠ k → G m = G' m) : FaceOK J n G ↔ FaceOK J n G' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombCyclic».«faceOK_congr» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_faceOK_congr_1857042b9c83
