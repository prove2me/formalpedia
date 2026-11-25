-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__not_exc_97c622bd5aa4
-- name    : P2M_Formalism_BasicNotions_Examples__not_exc_97c622bd5aa4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:23.899088+00:00
-- url     : https://prove2.me/theorems/517e435a-d069-4089-b4c1-012f5169f68b
-- title:
--   P2 M Formalism Basic Notions Examples  not exc 97c622bd5aa4: P2 M Formalism Basic Notions Examples  not exc 97c622bd5aa4
-- statement:
--   The P2 M Formalism Basic Notions Examples  not exc 97c622bd5aa4 construction uses the P2 M Formalism Basic Notions Examples  not exc 97c622bd5aa4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L545-L552
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L545-L552

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

theorem P2M_Formalism_BasicNotions_Examples__not_exc_97c622bd5aa4 {g d l k : ℕ} (h1 : ¬ l ^ (k + 1) ∣ g ^ d - 1) (h2 : l ^ (4 * k) ≤ g ^ d) :
    ¬ Formalism.CyclotomicNorms.Exc g d l := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«not_exc» := P2M_Formalism_BasicNotions_Examples__not_exc_97c622bd5aa4
