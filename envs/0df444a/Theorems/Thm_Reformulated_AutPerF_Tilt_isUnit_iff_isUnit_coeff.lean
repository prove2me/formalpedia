-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Tilt_isUnit_iff_isUnit_coeff
-- name    : Reformulated.AutPerF.Tilt.isUnit_iff_isUnit_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:12:04.301951+00:00
-- url     : https://prove2.me/theorems/afe06715-c495-4dc9-a811-0e200302901a
-- title:
--   Tilt: is Unit iff is Unit coeff
-- statement:
--   The Tilt construction uses the is Unit iff is Unit coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L91-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L91-L105

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

theorem Reformulated.AutPerF.Tilt.isUnit_iff_isUnit_coeff [IsLocalRing R] (a : R) :
    IsUnit (Ideal.Quotient.mk (span {(p : R)}) a) ↔ IsUnit a := by sorry
