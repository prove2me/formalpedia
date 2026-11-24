-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_smul_quot_mk_2882e2e1b3cb
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_smul_quot_mk_2882e2e1b3cb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:05.178318+00:00
-- url     : https://prove2.me/theorems/63acb553-8295-4bf2-9c28-215b88293897
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration smul quot mk 2882e2e1b3cb: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration smul quot mk 2882e2e1b3cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration smul quot mk 2882e2e1b3cb construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration smul quot mk 2882e2e1b3cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L194-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L194-L196

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
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
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} {ι : K → Type} {F : Type u} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_smul_quot_mk_2882e2e1b3cb (I : Ideal (MRing ι F)) (r x : MRing ι F) :
    r • Ideal.Quotient.mk I x = Ideal.Quotient.mk I (r * x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«smul_quot_mk» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_smul_quot_mk_2882e2e1b3cb
