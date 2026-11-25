-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_mapDomain_1cf518418e18
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_mapDomain_1cf518418e18
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:59.116992+00:00
-- url     : https://prove2.me/theorems/76a0efb4-3a5d-417f-afb5-1d4a12ec948a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers weight map Domain 1cf518418e18: P2 M Ground Theory Heights  Heights Field Numbers weight map Domain 1cf518418e18
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers weight map Domain 1cf518418e18 construction uses the P2 M Ground Theory Heights  Heights Field Numbers weight map Domain 1cf518418e18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L43-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)
variable [DecidableEq K] [DecidableEq K']
omit [DecidableEq K] [DecidableEq K']

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_mapDomain_1cf518418e18 {σ τ M : Type*} [AddCommMonoid M] (w : τ → M) (g : σ → τ)
    (d : σ →₀ ℕ) : Finsupp.weight w (Finsupp.mapDomain g d) = Finsupp.weight (w ∘ g) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«weight_mapDomain» := P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_mapDomain_1cf518418e18
