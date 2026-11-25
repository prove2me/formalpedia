-- Prove2me | Theorems.Thm_Reformulated_AutPerF_mem_span_natCast_pow_iff
-- name    : Reformulated.AutPerF.mem_span_natCast_pow_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:16.05831+00:00
-- url     : https://prove2.me/theorems/6e9b9519-6645-4774-953a-d85c1bfadad2
-- title:
--   Aut Per F: mem span nat Cast pow iff
-- statement:
--   The Aut Per F construction uses the mem span nat Cast pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L193-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L193-L195

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
variable {A Q : Type*} [CommRing A] [CommRing Q]

theorem Reformulated.AutPerF.mem_span_natCast_pow_iff {D : Type*} [CommRing D] (p n : ℕ) (x : D) :
    x ∈ (span {(p : D)} ^ n • ⊤ : Submodule D D) ↔ (p : D) ^ n ∣ x := by sorry
