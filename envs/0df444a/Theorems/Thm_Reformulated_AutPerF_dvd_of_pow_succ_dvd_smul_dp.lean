-- Prove2me | Theorems.Thm_Reformulated_AutPerF_dvd_of_pow_succ_dvd_smul_dp
-- name    : Reformulated.AutPerF.dvd_of_pow_succ_dvd_smul_dp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:23:02.589834+00:00
-- url     : https://prove2.me/theorems/18df70fb-f8d9-4a09-b890-87cf0d7eb901
-- title:
--   Aut Per F: dvd of pow succ dvd smul dp
-- statement:
--   The Aut Per F construction uses the dvd of pow succ dvd smul dp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L109-L113

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

theorem Reformulated.AutPerF.dvd_of_pow_succ_dvd_smul_dp {m : ℕ} {a : A}
    (h : algebraMap A B ξ ^ (m + 1) ∣ a • dp m (algebraMap A B ξ)) : ξ ∣ a := by sorry
