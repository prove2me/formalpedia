-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Tilt_isUnit_iff_isUnit_coeff_zero
-- name    : Reformulated.AutPerF.Tilt.isUnit_iff_isUnit_coeff_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:01.89481+00:00
-- url     : https://prove2.me/theorems/8a18e633-9b2b-40f1-ba9f-399ab034f462
-- title:
--   Tilt: is Unit iff is Unit coeff zero
-- statement:
--   The Tilt construction uses the is Unit iff is Unit coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L173-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L173-L174

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
open Reformulated.AutPerF.Tilt
variable [IsDomain R]
variable [ValuationRing R]

theorem Reformulated.AutPerF.Tilt.isUnit_iff_isUnit_coeff_zero (x : Tilt p R) : IsUnit x ↔ IsUnit (PreTilt.coeff 0 x) := by sorry
