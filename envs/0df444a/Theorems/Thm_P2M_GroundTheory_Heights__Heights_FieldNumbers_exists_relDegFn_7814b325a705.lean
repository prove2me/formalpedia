-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_relDegFn_7814b325a705
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_relDegFn_7814b325a705
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:54:56.908014+00:00
-- url     : https://prove2.me/theorems/9a504c07-3585-4a5e-aff0-7a2a9a0ced04
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers exists rel Deg Fn 7814b325a705: P2 M Ground Theory Heights  Heights Field Numbers exists rel Deg Fn 7814b325a705
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers exists rel Deg Fn 7814b325a705 construction uses the P2 M Ground Theory Heights  Heights Field Numbers exists rel Deg Fn 7814b325a705 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsSemilocalLengthSum.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsSemilocalLengthSum.lean#L39-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLengthSum
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
variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_relDegFn_7814b325a705 :
    ∃ d : Ideal (MRing ι' F) → ℕ, ∀ W' (hW' : IsMultiProjPrime W'),
      haveI := hW'.isPrime
      d W' = relDeg j W' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«exists_relDegFn» := P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_relDegFn_7814b325a705
