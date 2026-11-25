-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_quotient_span_sub_b356f7ceefe4
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_quotient_span_sub_b356f7ceefe4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:42.776283+00:00
-- url     : https://prove2.me/theorems/df25cb01-6e30-5740-86c6-2cd7449f9898
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas card quotient span sub b356f7ceefe4: P2 M Ground Theory Heights  Heights Lattice Lemmas card quotient span sub b356f7ceefe4
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas card quotient span sub b356f7ceefe4 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas card quotient span sub b356f7ceefe4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSublattice.lean#L22-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSublattice.lean#L22-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSublattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField GroundTheory.Heights₂.Heights
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_quotient_span_sub_b356f7ceefe4 {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E]
    [Module (𝓞 K) E] (F : Submodule (𝓞 K) E) {ι : Type*} (s : ι → F) :
    Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range fun i ↦ (s i : E))) =
      Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) * Nat.card (E ⧸ F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«card_quotient_span_sub» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_quotient_span_sub_b356f7ceefe4
