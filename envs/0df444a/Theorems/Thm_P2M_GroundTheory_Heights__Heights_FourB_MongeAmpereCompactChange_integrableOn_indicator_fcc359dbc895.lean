-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereCompactChange_integrableOn_indicator_fcc359dbc895
-- name    : P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereCompactChange_integrableOn_indicator_fcc359dbc895
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:41.329747+00:00
-- url     : https://prove2.me/theorems/09026040-5b4b-49e6-90ae-08cf1f927468
-- title:
--   P2 M Ground Theory Heights  Heights Four B Monge Ampere Compact Change integrable On indicator fcc359dbc895: P2 M Ground Theory Heights  Heights Four B Monge Ampere Compact Change integrable On indica
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Monge Ampere Compact Change integrable On indicator fcc359dbc895 construction uses the P2 M Ground Theory Heights  Heights Four B Monge Ampere Compact Change integrable On indicator fcc359dbc895 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereCompactChange.lean#L24-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereCompactChange.lean#L24-L63

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

theorem P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereCompactChange_integrableOn_indicator_fcc359dbc895 [T2Space X] (A : FinHolAtlas e X) (χ : ChartPartition A)
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (k : Fin A.n) {K : Set X}
    (hK : IsCompact K) :
    IntegrableOn (fun y => χ.χ k ((A.chart k).symm y) * K.indicator 1 ((A.chart k).symm y) *
      locDens A Ψ k y) (A.chart k).target := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«MongeAmpereCompactChange».«integrableOn_indicator» := P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereCompactChange_integrableOn_indicator_fcc359dbc895
