-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_isUnit_iff_isUnit_theta
-- name    : Reformulated.AutPerF.Ainf.isUnit_iff_isUnit_theta
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:32:28.342161+00:00
-- url     : https://prove2.me/theorems/51627707-7d89-4ca0-bf73-32860adb80a1
-- title:
--   Ainf: is Unit iff is Unit theta
-- statement:
--   The Ainf construction uses the is Unit iff is Unit theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L252-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L252-L254

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
variable [ValuationRing R]

theorem Reformulated.AutPerF.Ainf.isUnit_iff_isUnit_theta (x : Ainf p R) : IsUnit x ↔ IsUnit (theta p R x) := by sorry
