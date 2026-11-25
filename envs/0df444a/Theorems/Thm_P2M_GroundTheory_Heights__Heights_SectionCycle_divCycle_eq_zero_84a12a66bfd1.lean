-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_divCycle_eq_zero_84a12a66bfd1
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_divCycle_eq_zero_84a12a66bfd1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:50.829834+00:00
-- url     : https://prove2.me/theorems/1513d949-0557-43e0-af98-b9d58eb48769
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle div Cycle eq zero 84a12a66bfd1: P2 M Ground Theory Heights  Heights Section Cycle div Cycle eq zero 84a12a66bfd1
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle div Cycle eq zero 84a12a66bfd1 construction uses the P2 M Ground Theory Heights  Heights Section Cycle div Cycle eq zero 84a12a66bfd1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L71-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {K : Type*} {κ : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_divCycle_eq_zero_84a12a66bfd1 {I W : Ideal (NumbersDVR.MRing κ R)} (f : NumbersDVR.MRing κ R)
    (h : ¬ (W.IsPrime ∧ NumbersDVR.IsRelevant W ∧ I ≤ W)) : NumbersDVR.divCycle I f W = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«divCycle_eq_zero» := P2M_GroundTheory_Heights__Heights_SectionCycle_divCycle_eq_zero_84a12a66bfd1
