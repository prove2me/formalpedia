-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_isUnit_iff_isUnit_coeff
-- name    : Reformulated.AutPerF.Ainf.isUnit_iff_isUnit_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:42.698447+00:00
-- url     : https://prove2.me/theorems/c465980b-00e3-4788-9b42-a5ac9574c422
-- title:
--   Ainf: is Unit iff is Unit coeff
-- statement:
--   The Ainf construction uses the is Unit iff is Unit coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L218-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L218-L228

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
omit [IsAdicComplete (span {(p : R)}) R]

theorem Reformulated.AutPerF.Ainf.isUnit_iff_isUnit_coeff (x : Ainf p R) : IsUnit x ↔ IsUnit (x.coeff 0) := by sorry
