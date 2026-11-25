-- Prove2me | Theorems.Thm_Reformulated_AutPerF_mem_dpSpan_Ici
-- name    : Reformulated.AutPerF.mem_dpSpan_Ici
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:18.13705+00:00
-- url     : https://prove2.me/theorems/3bf70426-e7b4-5f87-b120-8a97e99ab72a
-- title:
--   Aut Per F: mem dp Span Ici
-- statement:
--   The Aut Per F construction uses the mem dp Span Ici property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L115-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L115-L125

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
variable [IsDomain B] (h0 : algebraMap A B ξ ≠ 0)
  (hξ : ∀ a : A, algebraMap A B ξ ∣ algebraMap A B a → ξ ∣ a)
include h0 hξ

theorem Reformulated.AutPerF.mem_dpSpan_Ici {m : ℕ} {z : B} (hz : z ∈ dpSpan B ξ Set.univ)
    (h : algebraMap A B ξ ^ m ∣ z) : z ∈ dpSpan B ξ (Set.Ici m) := by sorry
