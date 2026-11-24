-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_relDim_eq_int_8d437d865d06
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_relDim_eq_int_8d437d865d06
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:38.241015+00:00
-- url     : https://prove2.me/theorems/36c87d03-6e85-4c3a-8779-742c315c6bfb
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted rel Dim eq int 8d437d865d06: P2 M Ground Theory Heights  Heights Field Numbers PFContracted rel Dim eq int 8d437d865d06
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted rel Dim eq int 8d437d865d06 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted rel Dim eq int 8d437d865d06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L162-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L162-L166

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_relDim_eq_int_8d437d865d06 [Fintype K] {Q : Ideal (MRing ι F)} {D : ℕ}
    (hD : ringKrullDim (MRing ι F ⧸ Q) = D) :
    relDim Q = ((((D : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«relDim_eq_int» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_relDim_eq_int_8d437d865d06
