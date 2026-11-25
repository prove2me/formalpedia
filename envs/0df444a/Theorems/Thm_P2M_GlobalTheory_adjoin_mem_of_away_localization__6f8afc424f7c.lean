-- Prove2me | Theorems.Thm_P2M_GlobalTheory_adjoin_mem_of_away_localization__6f8afc424f7c
-- name    : P2M_GlobalTheory_adjoin_mem_of_away_localization__6f8afc424f7c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:06.587373+00:00
-- url     : https://prove2.me/theorems/acec56a7-a7e9-4335-ac34-10a37c6686d8
-- title:
--   P2 M Global Theory adjoin mem of away localization  6f8afc424f7c: P2 M Global Theory adjoin mem of away localization  6f8afc424f7c
-- statement:
--   The P2 M Global Theory adjoin mem of away localization  6f8afc424f7c construction uses the P2 M Global Theory adjoin mem of away localization  6f8afc424f7c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowMulMemAdjoinOfLocalizationAway.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowMulMemAdjoinOfLocalizationAway.lean#L48-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowMulMemAdjoinOfLocalizationAway
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Algebra

theorem P2M_GlobalTheory_adjoin_mem_of_away_localization__6f8afc424f7c : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (T : Set A) (b : A), algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T) → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by sorry

alias «GlobalTheory».«adjoin_mem_of_away_localization'» := P2M_GlobalTheory_adjoin_mem_of_away_localization__6f8afc424f7c
