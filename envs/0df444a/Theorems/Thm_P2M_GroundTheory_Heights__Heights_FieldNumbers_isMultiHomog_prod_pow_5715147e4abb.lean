-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_prod_pow_5715147e4abb
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_prod_pow_5715147e4abb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:23.311676+00:00
-- url     : https://prove2.me/theorems/2249633f-1b78-480a-b031-1b0b48974e23
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog prod pow 5715147e4abb: P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog prod pow 5715147e4abb
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog prod pow 5715147e4abb construction uses the P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog prod pow 5715147e4abb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PExistsForm.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PExistsForm.lean#L11-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_prod_pow_5715147e4abb {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*}
    [CommRing R] (i : ∀ k, ι k) (n : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι R) ^ n k) n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«isMultiHomog_prod_pow» := P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_prod_pow_5715147e4abb
