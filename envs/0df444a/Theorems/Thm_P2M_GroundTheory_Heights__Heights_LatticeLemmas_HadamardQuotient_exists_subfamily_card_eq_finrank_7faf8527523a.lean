-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardQuotient_exists_subfamily_card_eq_finrank_7faf8527523a
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardQuotient_exists_subfamily_card_eq_finrank_7faf8527523a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:23.404814+00:00
-- url     : https://prove2.me/theorems/00b72db8-49d6-559e-88e0-b7abb1f9145e
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas Hadamard Quotient exists subfamily card eq finrank 7faf8527523a: P2 M Ground Theory Heights  Heights Lattice Lemmas Hadamard Quotient exists subfamil
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas Hadamard Quotient exists subfamily card eq finrank 7faf8527523a construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas Hadamard Quotient exists subfamily card eq finrank 7faf8527523a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardQuotient.lean#L16-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardQuotient.lean#L16-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardQuotient
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Module Submodule
open GroundTheory.Heights₂.Heights
universe u v w
noncomputable section
open GroundTheory.Heights₂.Heights.LatticeLemmas.HadamardQuotient

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardQuotient_exists_subfamily_card_eq_finrank_7faf8527523a {R M : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (F : Submodule R M)
    {ι : Type*} (x : ι → M) (hx : finrank R (span R (Set.range x)) = finrank R M) :
    ∃ s : Set ι, LinearIndepOn R (F.mkQ ∘ x) s ∧ Finite s ∧ Nat.card s = finrank R (M ⧸ F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«HadamardQuotient».«exists_subfamily_card_eq_finrank» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardQuotient_exists_subfamily_card_eq_finrank_7faf8527523a
