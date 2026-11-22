-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__lucas_list_6f32cc34af5b
-- name    : P2M_Formalism_BasicNotions_Examples__lucas_list_6f32cc34af5b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:44.752627+00:00
-- url     : https://prove2.me/theorems/28d8b7c6-8fd3-4f56-a362-4a4b0c6afb93
-- title:
--   P2 M Formalism Basic Notions Examples  lucas list 6f32cc34af5b: P2 M Formalism Basic Notions Examples  lucas list 6f32cc34af5b
-- statement:
--   The P2 M Formalism Basic Notions Examples  lucas list 6f32cc34af5b construction uses the P2 M Formalism Basic Notions Examples  lucas list 6f32cc34af5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L12-L15

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

theorem P2M_Formalism_BasicNotions_Examples__lucas_list_6f32cc34af5b (n a : ℕ) (ps : List ℕ) (K : ℕ) (hd : n - 1 ∣ ps.prod ^ K) (hp : ∀ p ∈ ps, p.Prime)
    (h1 : (a : ZMod n) ^ (n - 1) = 1) (h2 : ∀ p ∈ ps, (a : ZMod n) ^ ((n - 1) / p) ≠ 1) : n.Prime := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«lucas_list» := P2M_Formalism_BasicNotions_Examples__lucas_list_6f32cc34af5b
