-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_eq_zero_89948f02be2c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_eq_zero_89948f02be2c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:13.972285+00:00
-- url     : https://prove2.me/theorems/220bb90c-7d9b-5d50-a857-4e5ce40921c4
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration mult At eq zero 89948f02be2c: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration mult At eq zero 89948f02be2c
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration mult At eq zero 89948f02be2c construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration mult At eq zero 89948f02be2c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L198-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L198-L212

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_eq_zero_89948f02be2c {A W : Ideal (MRing ι F)} [W.IsPrime] (h : ¬ A ≤ W) : multAt A W = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«multAt_eq_zero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_eq_zero_89948f02be2c
