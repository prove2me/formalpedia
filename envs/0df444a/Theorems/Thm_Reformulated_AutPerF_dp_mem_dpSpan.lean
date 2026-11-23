-- Prove2me | Theorems.Thm_Reformulated_AutPerF_dp_mem_dpSpan
-- name    : Reformulated.AutPerF.dp_mem_dpSpan
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:15.03079+00:00
-- url     : https://prove2.me/theorems/498acbcc-11de-445d-9b4b-6ef164717464
-- title:
--   Aut Per F: dp mem dp Span
-- statement:
--   The Aut Per F construction uses the dp mem dp Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L59-L60

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
variable {B : Type*} [CommRing B] [Algebra ℚ B]
variable {A : Type*} [CommRing A] [Algebra A B]
variable {ξ : A}

theorem Reformulated.AutPerF.dp_mem_dpSpan {s : Set ℕ} {m : ℕ} (h : m ∈ s) : dp m (algebraMap A B ξ) ∈ dpSpan B ξ s := by sorry
