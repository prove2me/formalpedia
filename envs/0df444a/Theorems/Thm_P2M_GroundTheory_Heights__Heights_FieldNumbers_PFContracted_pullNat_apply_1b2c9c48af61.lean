-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_pullNat_apply_1b2c9c48af61
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_pullNat_apply_1b2c9c48af61
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:46.402106+00:00
-- url     : https://prove2.me/theorems/c290d9d8-adc2-4945-8565-625b4f9e4f22
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted pull Nat apply 1b2c9c48af61: P2 M Ground Theory Heights  Heights Field Numbers PFContracted pull Nat apply 1b2c9c48af61
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted pull Nat apply 1b2c9c48af61 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted pull Nat apply 1b2c9c48af61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L221-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L221-L232

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
variable (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_pullNat_apply_1b2c9c48af61 (e : K → ℕ) (k' : K') :
    (pullNat K K' j e k' : ℤ) = Function.extend j (fun κ => (e κ : ℤ)) 0 k' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«pullNat_apply» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_pullNat_apply_1b2c9c48af61
