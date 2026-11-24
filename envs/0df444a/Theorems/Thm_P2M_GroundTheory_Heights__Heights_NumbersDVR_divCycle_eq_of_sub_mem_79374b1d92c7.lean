-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_sub_mem_79374b1d92c7
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_sub_mem_79374b1d92c7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:46.467852+00:00
-- url     : https://prove2.me/theorems/9db73b05-8b0e-4601-8da6-c6de6bf5078d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq of sub mem 79374b1d92c7: P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq of sub mem 79374b1d92c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq of sub mem 79374b1d92c7 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq of sub mem 79374b1d92c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PRepresentative.lean#L108-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PRepresentative.lean#L108-L127

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_sub_mem_79374b1d92c7 {P : Ideal (MRing ι R)} {x y : MRing ι R} (h : x - y ∈ P) :
    divCycle P x = divCycle P y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«divCycle_eq_of_sub_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_sub_mem_79374b1d92c7
