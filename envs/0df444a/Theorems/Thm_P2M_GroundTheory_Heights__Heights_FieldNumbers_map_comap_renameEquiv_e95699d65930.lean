-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_map_comap_renameEquiv_e95699d65930
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_map_comap_renameEquiv_e95699d65930
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:16.733006+00:00
-- url     : https://prove2.me/theorems/a71cdabb-4112-408f-86be-fd9d3faa2ecd
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers map comap rename Equiv e95699d65930: P2 M Ground Theory Heights  Heights Field Numbers map comap rename Equiv e95699d65930
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers map comap rename Equiv e95699d65930 construction uses the P2 M Ground Theory Heights  Heights Field Numbers map comap rename Equiv e95699d65930 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameHilbFn.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameHilbFn.lean#L14-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameHilbFn
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_map_comap_renameEquiv_e95699d65930 {F : Type u} [Field F] {S K' : Type} {κ : S → Type}
    {ι' : K' → Type} (σ : (Σ s, κ s) ≃ (Σ k', ι' k')) (P : Ideal (MRing ι' F)) :
    (P.comap (rename σ)).map (renameEquiv F σ) = P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«map_comap_renameEquiv» := P2M_GroundTheory_Heights__Heights_FieldNumbers_map_comap_renameEquiv_e95699d65930
