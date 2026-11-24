-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_idealCycle_4d914ac33675
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_idealCycle_4d914ac33675
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:35.154445+00:00
-- url     : https://prove2.me/theorems/8a794ad4-8a41-4246-8c86-9dfcf509a785
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq ideal Cycle 4d914ac33675: P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq ideal Cycle 4d914ac33675
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq ideal Cycle 4d914ac33675 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq ideal Cycle 4d914ac33675 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsCN.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsCN.lean#L32-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
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
variable {K : Type*}
variable {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_idealCycle_4d914ac33675 {R : Type*} [CommRing R] (P : Ideal (MRing ι R)) (f : MRing ι R) :
    divCycle P f = idealCycle (P ⊔ Ideal.span {f}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«divCycle_eq_idealCycle» := P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_idealCycle_4d914ac33675
