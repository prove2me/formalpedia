-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ringKrullDim_mvPolynomial_le_954429728b2c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ringKrullDim_mvPolynomial_le_954429728b2c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:24.703151+00:00
-- url     : https://prove2.me/theorems/a12e82ba-34ac-448f-82ec-3cd4c647095c
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration ring Krull Dim mv Polynomial le 954429728b2c: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration ring Krull Dim mv Po
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration ring Krull Dim mv Polynomial le 954429728b2c construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration ring Krull Dim mv Polynomial le 954429728b2c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L313-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L313-L324

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ringKrullDim_mvPolynomial_le_954429728b2c (F : Type u) [Field F] (σ : Type) [Finite σ] :
    ringKrullDim (MvPolynomial σ F) ≤ Nat.card σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«ringKrullDim_mvPolynomial_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ringKrullDim_mvPolynomial_le_954429728b2c
