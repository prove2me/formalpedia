-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Level_M__pos_9f8643595328
-- name    : P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Level_M__pos_9f8643595328
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:05:59.347179+00:00
-- url     : https://prove2.me/theorems/12ee44a0-1912-4a0b-972c-fe93f9eefd08
-- title:
--   P2 M Global Theory Indefinite Row Side Full Hecke Host Conjugate Ideal Level M  pos 9f8643595328: P2 M Global Theory Indefinite Row Side Full Hecke Host Conjugate Ideal Level M  pos 9f8643595328
-- statement:
--   The P2 M Global Theory Indefinite Row Side Full Hecke Host Conjugate Ideal Level M  pos 9f8643595328 construction uses the P2 M Global Theory Indefinite Row Side Full Hecke Host Conjugate Ideal Level M  pos 9f8643595328 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HostConjugateIdeal.lean#L198-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HostConjugateIdeal.lean#L198-L199

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

theorem P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Level_M__pos_9f8643595328 (L : Level H) : 0 < L.M' := by sorry

alias «GlobalTheory».«IndefiniteRowSideFullHecke».«HostConjugateIdeal».«Level».«M'_pos» := P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Level_M__pos_9f8643595328
