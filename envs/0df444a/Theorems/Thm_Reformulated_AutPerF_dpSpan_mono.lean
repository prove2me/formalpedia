-- Prove2me | Theorems.Thm_Reformulated_AutPerF_dpSpan_mono
-- name    : Reformulated.AutPerF.dpSpan_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:24.759512+00:00
-- url     : https://prove2.me/theorems/73e8aeb8-48eb-47e3-9a7a-5d6d20a4e9fc
-- title:
--   Aut Per F: dp Span mono
-- statement:
--   The Aut Per F construction uses the dp Span mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L56-L57

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

theorem Reformulated.AutPerF.dpSpan_mono {s t : Set ℕ} (h : s ⊆ t) : dpSpan B ξ s ≤ dpSpan B ξ t := by sorry
