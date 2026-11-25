-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_ker_theta_eq_span_teich_sub_one
-- name    : Reformulated.AutPerF.BdRPlus.ker_theta_eq_span_teich_sub_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:12:03.037379+00:00
-- url     : https://prove2.me/theorems/0f7284ba-f118-5c15-b14b-f56f67befdd9
-- title:
--   Bd RPlus: ker theta eq span teich sub one
-- statement:
--   The Bd RPlus construction uses the ker theta eq span teich sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L243-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L243-L251

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
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
open Reformulated Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]
open Reformulated.AutPerF.BdRPlus
variable [IsAlgClosed (FractionRing R)]

theorem Reformulated.AutPerF.BdRPlus.ker_theta_eq_span_teich_sub_one {ε : tateModule p R} (hε : IsPrimitive ε) :
    RingHom.ker (theta p R) = span {algebraMap (Ainf p R) (BdRPlus p R) (Ainf.teich p ε.1 - 1)} := by sorry
