-- Prove2me | Theorems.Thm_P2M_Reformulated_AutPerF_eval__adicLog_f7990fb6ad72
-- name    : P2M_Reformulated_AutPerF_eval__adicLog_f7990fb6ad72
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:18:27.269773+00:00
-- url     : https://prove2.me/theorems/9cb2b551-fe9e-4aea-94e4-667fbd835902
-- title:
--   P2 M Reformulated Aut Per F eval  adic Log f7990fb6ad72: P2 M Reformulated Aut Per F eval  adic Log f7990fb6ad72
-- statement:
--   The P2 M Reformulated Aut Per F eval  adic Log f7990fb6ad72 construction uses the P2 M Reformulated Aut Per F eval  adic Log f7990fb6ad72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L78-L81

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
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

theorem P2M_Reformulated_AutPerF_eval__adicLog_f7990fb6ad72 [Algebra ℚ A] (I : Ideal A) (u : AdicCompletion I A)
    (hu : AdicCompletion.evalOneₐ I u = 1) (n : ℕ) :
    AdicCompletion.evalₐ I n (adicLog I u hu) = truncLog n (AdicCompletion.evalₐ I n (u - 1)) := by sorry

alias «Reformulated».«AutPerF».«evalₐ_adicLog» := P2M_Reformulated_AutPerF_eval__adicLog_f7990fb6ad72
