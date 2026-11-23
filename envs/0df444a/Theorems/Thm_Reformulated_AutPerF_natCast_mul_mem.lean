-- Prove2me | Theorems.Thm_Reformulated_AutPerF_natCast_mul_mem
-- name    : Reformulated.AutPerF.natCast_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:28.018801+00:00
-- url     : https://prove2.me/theorems/d31c6c36-416a-48ff-bb41-722045800d3e
-- title:
--   Aut Per F: nat Cast mul mem
-- statement:
--   The Aut Per F construction uses the nat Cast mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L62-L63

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

theorem Reformulated.AutPerF.natCast_mul_mem {M : Submodule A B} (n : ℕ) {x : B} (h : x ∈ M) : (n : B) * x ∈ M := by sorry
