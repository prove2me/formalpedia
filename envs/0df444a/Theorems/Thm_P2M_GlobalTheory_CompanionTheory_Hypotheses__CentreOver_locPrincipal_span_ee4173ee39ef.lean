-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_span_ee4173ee39ef
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_span_ee4173ee39ef
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:27.733094+00:00
-- url     : https://prove2.me/theorems/298bd959-952f-4bb7-ba0b-8b3095e5b931
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal span ee4173ee39ef: P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal span ee4173ee39ef
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal span ee4173ee39ef construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal span ee4173ee39ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocPrincipalSpan.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocPrincipalSpan.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_span_ee4173ee39ef {A : Type} [CommRing A] {f : A} (hf : f ≠ 0) {p : Ideal A} (hp : p ≠ ⊤) :
    LocPrincipal (Ideal.span {f}) p := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«locPrincipal_span» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_span_ee4173ee39ef
