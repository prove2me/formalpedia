-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_hilbFn_top_eaf1d44ba056
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_hilbFn_top_eaf1d44ba056
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:01.898239+00:00
-- url     : https://prove2.me/theorems/7543383c-3c8a-51b9-8a67-6c6f0bd9b3ac
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration hilb Fn top eaf1d44ba056: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration hilb Fn top eaf1d44ba056
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration hilb Fn top eaf1d44ba056 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration hilb Fn top eaf1d44ba056 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L385-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L385-L391

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_hilbFn_top_eaf1d44ba056 (m : K → ℤ) : hilbFn (⊤ : Ideal (MRing ι F)) m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«hilbFn_top» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_hilbFn_top_eaf1d44ba056
