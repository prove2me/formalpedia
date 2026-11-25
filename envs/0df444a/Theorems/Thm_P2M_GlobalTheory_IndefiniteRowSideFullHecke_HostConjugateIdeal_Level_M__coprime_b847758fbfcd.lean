-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Level_M__coprime_b847758fbfcd
-- name    : P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Level_M__coprime_b847758fbfcd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:59.304528+00:00
-- url     : https://prove2.me/theorems/c5246416-da60-456a-850c-9e7545e4bd32
-- title:
--   P2 M Global Theory Indefinite Row Side Full Hecke Host Conjugate Ideal Level M  coprime b847758fbfcd: P2 M Global Theory Indefinite Row Side Full Hecke Host Conjugate Ideal Level M  coprime b847758fbf
-- statement:
--   The P2 M Global Theory Indefinite Row Side Full Hecke Host Conjugate Ideal Level M  coprime b847758fbfcd construction uses the P2 M Global Theory Indefinite Row Side Full Hecke Host Conjugate Ideal Level M  coprime b847758fbfcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HostConjugateIdeal.lean#L201-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HostConjugateIdeal.lean#L201-L202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level
variable {H : Host E}

theorem P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Level_M__coprime_b847758fbfcd (L : Level H) {p : ℕ} (hp : p.Prime) : Nat.Coprime p (L.M₀ p) := by sorry

alias «GlobalTheory».«IndefiniteRowSideFullHecke».«HostConjugateIdeal».«Level».«M₀_coprime» := P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Level_M__coprime_b847758fbfcd
