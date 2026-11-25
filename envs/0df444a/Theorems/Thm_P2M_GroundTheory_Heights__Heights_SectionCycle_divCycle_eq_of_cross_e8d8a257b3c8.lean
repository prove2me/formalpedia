-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_divCycle_eq_of_cross_e8d8a257b3c8
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_divCycle_eq_of_cross_e8d8a257b3c8
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:59.749727+00:00
-- url     : https://prove2.me/theorems/a5188f90-aed5-4803-9eed-657f3ea46418
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle div Cycle eq of cross e8d8a257b3c8: P2 M Ground Theory Heights  Heights Section Cycle div Cycle eq of cross e8d8a257b3c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle div Cycle eq of cross e8d8a257b3c8 construction uses the P2 M Ground Theory Heights  Heights Section Cycle div Cycle eq of cross e8d8a257b3c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L78-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L78-L119

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

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_divCycle_eq_of_cross_e8d8a257b3c8 (I : Ideal (NumbersDVR.MRing κ R)) {f g f' g' : NumbersDVR.MRing κ R}
    {W : Ideal (NumbersDVR.MRing κ R)} [W.IsPrime] (hf' : f' ∉ W) (hg' : g' ∉ W)
    (hrel : f * g' - f' * g ∈ I) : NumbersDVR.divCycle I f W = NumbersDVR.divCycle I g W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«divCycle_eq_of_cross» := P2M_GroundTheory_Heights__Heights_SectionCycle_divCycle_eq_of_cross_e8d8a257b3c8
