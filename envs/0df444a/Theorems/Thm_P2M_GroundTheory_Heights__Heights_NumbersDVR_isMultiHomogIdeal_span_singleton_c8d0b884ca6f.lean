-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_span_singleton_c8d0b884ca6f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_span_singleton_c8d0b884ca6f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:51.221244+00:00
-- url     : https://prove2.me/theorems/fcff96e9-13b3-48c9-b398-56597cdf6338
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal span singleton c8d0b884ca6f: P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal span singleton c8d0b884ca6f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal span singleton c8d0b884ca6f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal span singleton c8d0b884ca6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsMultiHomogIdealSpanSingleton.lean#L144-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsMultiHomogIdealSpanSingleton.lean#L144-L154

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_span_singleton_c8d0b884ca6f {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*}
    [CommRing R] {x : MRing ι R} {e : K → ℕ} (hx : IsMultiHomog x e) :
    IsMultiHomogIdeal (Ideal.span {x}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isMultiHomogIdeal_span_singleton» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_span_singleton_c8d0b884ca6f
