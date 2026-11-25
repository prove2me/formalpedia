-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_self_40c08fc02462
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_self_40c08fc02462
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:01.057803+00:00
-- url     : https://prove2.me/theorems/db9f3a11-fe27-4f3f-b184-41446bc7ec8f
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration mult At self 40c08fc02462: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration mult At self 40c08fc02462
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration mult At self 40c08fc02462 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration mult At self 40c08fc02462 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L214-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L214-L254

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_self_40c08fc02462 (W : Ideal (MRing ι F)) [hW : W.IsPrime] : multAt W W = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«multAt_self» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_self_40c08fc02462
