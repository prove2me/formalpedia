-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_omega_mul
-- name    : Reformulated.AutPerF.Ainf.omega_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:30.665801+00:00
-- url     : https://prove2.me/theorems/0a8dace2-91da-4950-acb5-9f5d1109cd71
-- title:
--   Ainf: omega mul
-- statement:
--   The Ainf construction uses the omega mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L365-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L365-L367

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

theorem Reformulated.AutPerF.Ainf.omega_mul (ε : tateModule p R) :
    omega ε * (teich p (tateRoot ε) - 1) = teich p ε.1 - 1 := by sorry
