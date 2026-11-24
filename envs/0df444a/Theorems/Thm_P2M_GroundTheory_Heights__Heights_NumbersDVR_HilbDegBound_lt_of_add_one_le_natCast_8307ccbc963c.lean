-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_lt_of_add_one_le_natCast_8307ccbc963c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_lt_of_add_one_le_natCast_8307ccbc963c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:54.113706+00:00
-- url     : https://prove2.me/theorems/81b955ec-aee5-4672-8b63-ea7853732d99
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound lt of add one le nat Cast 8307ccbc963c: P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound lt of add one le nat Cast 8307ccbc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound lt of add one le nat Cast 8307ccbc963c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound lt of add one le nat Cast 8307ccbc963c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbDegBound.lean#L49-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbDegBound.lean#L49-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHilbDegBound
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
open GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_lt_of_add_one_le_natCast_8307ccbc963c {x : WithBot ℕ∞} {N : ℕ} (h : x + 1 ≤ N) : x < N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HilbDegBound».«lt_of_add_one_le_natCast» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_lt_of_add_one_le_natCast_8307ccbc963c
