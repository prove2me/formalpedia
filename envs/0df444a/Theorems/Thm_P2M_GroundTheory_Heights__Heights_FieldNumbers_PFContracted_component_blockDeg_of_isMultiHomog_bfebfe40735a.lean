-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_component_blockDeg_of_isMultiHomog_bfebfe40735a
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_component_blockDeg_of_isMultiHomog_bfebfe40735a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:55.370565+00:00
-- url     : https://prove2.me/theorems/4719390a-b867-5dfc-82b7-ea6f124bc91a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted component block Deg of is Multi Homog bfebfe40735a: P2 M Ground Theory Heights  Heights Field Numbers PFContracted component block Deg of
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted component block Deg of is Multi Homog bfebfe40735a construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted component block Deg of is Multi Homog bfebfe40735a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L39-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_component_blockDeg_of_isMultiHomog_bfebfe40735a {p : MRing ι F} {b : K → ℕ} (hp : IsMultiHomog p b)
    (k : K) (n : ℕ) :
    weightedHomogeneousComponent (blockDeg k) n p = if b k = n then p else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«component_blockDeg_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_component_blockDeg_of_isMultiHomog_bfebfe40735a
