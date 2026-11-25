-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereCompactChange_step_5b97dcda69e7
-- name    : P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereCompactChange_step_5b97dcda69e7
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:25.78183+00:00
-- url     : https://prove2.me/theorems/4231ccab-29e5-4af4-b94c-dcdfa6707733
-- title:
--   P2 M Ground Theory Heights  Heights Four B Monge Ampere Compact Change step 5b97dcda69e7: P2 M Ground Theory Heights  Heights Four B Monge Ampere Compact Change step 5b97dcda69e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Monge Ampere Compact Change step 5b97dcda69e7 construction uses the P2 M Ground Theory Heights  Heights Four B Monge Ampere Compact Change step 5b97dcda69e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereCompactChange.lean#L65-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereCompactChange.lean#L65-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_CompactSupportStokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereCompactChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereCompactChange
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereCompactChange_step_5b97dcda69e7 [T2Space X] {n : ℕ} (A : FinHolAtlas (n + 1) X) (χ : ChartPartition A)
    (Ψ : Fin (n + 1) → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (a : Fin (n + 1)) (v : X → ℝ)
    (hv : A.Smooth v) (hvc : HasCompactSupport v) {K : Set X} (hK : IsCompact K)
    (hvK : tsupport v ⊆ K) :
    integralWith A χ (Function.update Ψ a (Ψ a + LocPot.ofFun v)) (K.indicator 1) =
      integralWith A χ Ψ (K.indicator 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«MongeAmpereCompactChange».«step» := P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereCompactChange_step_5b97dcda69e7
