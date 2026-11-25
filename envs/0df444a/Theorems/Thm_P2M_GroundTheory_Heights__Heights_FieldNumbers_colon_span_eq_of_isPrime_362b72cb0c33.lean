-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_colon_span_eq_of_isPrime_362b72cb0c33
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_colon_span_eq_of_isPrime_362b72cb0c33
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:24.912697+00:00
-- url     : https://prove2.me/theorems/01c4d8f0-b384-4877-bf19-922245ba1799
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers colon span eq of is Prime 362b72cb0c33: P2 M Ground Theory Heights  Heights Field Numbers colon span eq of is Prime 362b72cb0c33
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers colon span eq of is Prime 362b72cb0c33 construction uses the P2 M Ground Theory Heights  Heights Field Numbers colon span eq of is Prime 362b72cb0c33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L50-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbDegreeBound
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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_colon_span_eq_of_isPrime_362b72cb0c33 {P : Ideal (MRing ι F)} (hP : P.IsPrime) {s : MRing ι F}
    (hs : s ∉ P) : P.colon (Ideal.span {s}) = P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«colon_span_eq_of_isPrime» := P2M_GroundTheory_Heights__Heights_FieldNumbers_colon_span_eq_of_isPrime_362b72cb0c33
