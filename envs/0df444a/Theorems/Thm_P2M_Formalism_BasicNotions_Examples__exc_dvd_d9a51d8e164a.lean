-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exc_dvd_d9a51d8e164a
-- name    : P2M_Formalism_BasicNotions_Examples__exc_dvd_d9a51d8e164a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:10.626746+00:00
-- url     : https://prove2.me/theorems/90f17182-145f-4770-98b0-37f9b4d8ff83
-- title:
--   P2 M Formalism Basic Notions Examples  exc dvd d9a51d8e164a: P2 M Formalism Basic Notions Examples  exc dvd d9a51d8e164a
-- statement:
--   The P2 M Formalism Basic Notions Examples  exc dvd d9a51d8e164a construction uses the P2 M Formalism Basic Notions Examples  exc dvd d9a51d8e164a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L535-L543
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L535-L543

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Primes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂

theorem P2M_Formalism_BasicNotions_Examples__exc_dvd_d9a51d8e164a {g d l : ℕ} (hg : 1 ≤ g) (h1 : 1 ≤ d) (h9 : d ≤ 9) (h : Formalism.CyclotomicNorms.Exc g d l) : l ∣ prodPowSubOne g := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«exc_dvd» := P2M_Formalism_BasicNotions_Examples__exc_dvd_d9a51d8e164a
