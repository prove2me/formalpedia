-- Prove2me | Theorems.Thm_P2M_GlobalTheory_exists_algEquiv_pi_henselianLocalRing__cbd881570b99
-- name    : P2M_GlobalTheory_exists_algEquiv_pi_henselianLocalRing__cbd881570b99
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:07:15.420822+00:00
-- url     : https://prove2.me/theorems/cf29fff4-cb3c-4d77-b6d2-54f0567c59b1
-- title:
--   P2 M Global Theory exists alg Equiv pi henselian Local Ring  cbd881570b99: P2 M Global Theory exists alg Equiv pi henselian Local Ring  cbd881570b99
-- statement:
--   The P2 M Global Theory exists alg Equiv pi henselian Local Ring  cbd881570b99 construction uses the P2 M Global Theory exists alg Equiv pi henselian Local Ring  cbd881570b99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L430-L440
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L430-L440

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct

theorem P2M_GlobalTheory_exists_algEquiv_pi_henselianLocalRing__cbd881570b99.{v} (R : Type*) (S : Type v) [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] :
    ∃ (ι : Type v) (_ : Finite ι) (T : ι → Type v) (_ : ∀ i, CommRing (T i))
      (_ : ∀ i, Algebra R (T i)) (_ : S ≃ₐ[R] Π i, T i),
      ∀ i, HenselianLocalRing (T i) ∧ Module.Finite R (T i) := by sorry

alias «GlobalTheory».«exists_algEquiv_pi_henselianLocalRing».«» := P2M_GlobalTheory_exists_algEquiv_pi_henselianLocalRing__cbd881570b99
