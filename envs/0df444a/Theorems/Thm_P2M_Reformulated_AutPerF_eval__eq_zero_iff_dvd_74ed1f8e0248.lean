-- Prove2me | Theorems.Thm_P2M_Reformulated_AutPerF_eval__eq_zero_iff_dvd_74ed1f8e0248
-- name    : P2M_Reformulated_AutPerF_eval__eq_zero_iff_dvd_74ed1f8e0248
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:05:23.783108+00:00
-- url     : https://prove2.me/theorems/4573da57-a640-5ea3-ab47-4eacdebf9762
-- title:
--   P2 M Reformulated Aut Per F eval  eq zero iff dvd 74ed1f8e0248: P2 M Reformulated Aut Per F eval  eq zero iff dvd 74ed1f8e0248
-- statement:
--   The P2 M Reformulated Aut Per F eval  eq zero iff dvd 74ed1f8e0248 construction uses the P2 M Reformulated Aut Per F eval  eq zero iff dvd 74ed1f8e0248 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L17-L33

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
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
universe u v w
variable {A : Type u} [CommRing A]

theorem P2M_Reformulated_AutPerF_eval__eq_zero_iff_dvd_74ed1f8e0248 (a : A) (n : ℕ) (x : AdicCompletion (span {a}) A) :
    AdicCompletion.evalₐ (span {a}) n x = 0 ↔
      algebraMap A (AdicCompletion (span {a}) A) a ^ n ∣ x := by sorry

alias «Reformulated».«AutPerF».«evalₐ_eq_zero_iff_dvd» := P2M_Reformulated_AutPerF_eval__eq_zero_iff_dvd_74ed1f8e0248
