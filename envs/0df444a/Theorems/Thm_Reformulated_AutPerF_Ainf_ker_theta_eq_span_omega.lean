-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_ker_theta_eq_span_omega
-- name    : Reformulated.AutPerF.Ainf.ker_theta_eq_span_omega
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:32:33.725243+00:00
-- url     : https://prove2.me/theorems/ae064bc0-3ce8-4573-89f5-342f61a00335
-- title:
--   Ainf: ker theta eq span omega
-- statement:
--   The Ainf construction uses the ker theta eq span omega property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L419-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L419-L423

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
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
open Reformulated.AutPerF.Ainf
variable [IsDomain R]
variable [ValuationRing R] [CharZero R]

theorem Reformulated.AutPerF.Ainf.ker_theta_eq_span_omega [IsAlgClosed (FractionRing R)] {ε : tateModule p R}
    (hε : IsPrimitive ε) : RingHom.ker (theta p R) = span {omega ε} := by sorry
