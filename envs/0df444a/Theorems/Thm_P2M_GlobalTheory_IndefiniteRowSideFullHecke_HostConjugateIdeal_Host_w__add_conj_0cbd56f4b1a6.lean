-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Host_w__add_conj_0cbd56f4b1a6
-- name    : P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Host_w__add_conj_0cbd56f4b1a6
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:33.605897+00:00
-- url     : https://prove2.me/theorems/fc17429c-ae82-4d96-9bfe-5f712a7fccc5
-- title:
--   P2 M Global Theory Indefinite Row Side Full Hecke Host Conjugate Ideal Host w  add conj 0cbd56f4b1a6: P2 M Global Theory Indefinite Row Side Full Hecke Host Conjugate Ideal Host w  add conj 0cbd56f4b1
-- statement:
--   The P2 M Global Theory Indefinite Row Side Full Hecke Host Conjugate Ideal Host w  add conj 0cbd56f4b1a6 construction uses the P2 M Global Theory Indefinite Row Side Full Hecke Host Conjugate Ideal Host w  add conj 0cbd56f4b1a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HostConjugateIdeal.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HostConjugateIdeal.lean#L80-L84

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
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Host
variable (H : Host E)

theorem P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Host_w__add_conj_0cbd56f4b1a6 : H.w₀ + conjO E H.w₀ = 1 := by sorry

alias «GlobalTheory».«IndefiniteRowSideFullHecke».«HostConjugateIdeal».«Host».«w₀_add_conj» := P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Host_w__add_conj_0cbd56f4b1a6
