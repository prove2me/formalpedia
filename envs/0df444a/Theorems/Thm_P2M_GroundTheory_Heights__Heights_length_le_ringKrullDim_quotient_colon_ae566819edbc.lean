-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_le_ringKrullDim_quotient_colon_ae566819edbc
-- name    : P2M_GroundTheory_Heights__Heights_length_le_ringKrullDim_quotient_colon_ae566819edbc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:23.146915+00:00
-- url     : https://prove2.me/theorems/9e4be89d-76b2-4b54-b931-a625ad023f02
-- title:
--   P2 M Ground Theory Heights  Heights length le ring Krull Dim quotient colon ae566819edbc: P2 M Ground Theory Heights  Heights length le ring Krull Dim quotient colon ae566819edbc
-- statement:
--   The P2 M Ground Theory Heights  Heights length le ring Krull Dim quotient colon ae566819edbc construction uses the P2 M Ground Theory Heights  Heights length le ring Krull Dim quotient colon ae566819edbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CMDepthAssoc.lean#L9-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CMDepthAssoc.lean#L9-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing RingTheory.Sequence Pointwise

theorem P2M_GroundTheory_Heights__Heights_length_le_ringKrullDim_quotient_colon_ae566819edbc {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (rs : List R) : ∀ {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (y : M), y ≠ 0 →
      (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular M rs →
        (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R M) {y}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«length_le_ringKrullDim_quotient_colon» := P2M_GroundTheory_Heights__Heights_length_le_ringKrullDim_quotient_colon_ae566819edbc
