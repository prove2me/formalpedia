-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ringKrullDim_quotient_prime_066209f46a97
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ringKrullDim_quotient_prime_066209f46a97
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:46.920975+00:00
-- url     : https://prove2.me/theorems/5c391976-6ebd-4f66-ac2a-ec8f70f34233
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration ring Krull Dim quotient prime 066209f46a97: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration ring Krull Dim quotien
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration ring Krull Dim quotient prime 066209f46a97 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration ring Krull Dim quotient prime 066209f46a97 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L326-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L326-L332

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ringKrullDim_quotient_prime_066209f46a97 {R : Type*} [CommRing R] (Q : Ideal R) [hQ : Q.IsPrime] :
    ringKrullDim (R ⧸ Q) = (Order.coheight (⟨Q, hQ⟩ : PrimeSpectrum R) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«ringKrullDim_quotient_prime» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ringKrullDim_quotient_prime_066209f46a97
