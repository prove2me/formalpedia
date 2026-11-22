-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_xi_ne_zero
-- name    : Reformulated.AutPerF.Ainf.xi_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:11:50.971934+00:00
-- url     : https://prove2.me/theorems/3f34e8e5-3f99-40ef-a717-762d7f489e00
-- title:
--   Ainf: xi ne zero
-- statement:
--   The Ainf construction uses the xi ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L242-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L242-L248

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

theorem Reformulated.AutPerF.Ainf.xi_ne_zero [CharZero R] (ϖ : PFlat p R) : xi ϖ ≠ 0 := by sorry
