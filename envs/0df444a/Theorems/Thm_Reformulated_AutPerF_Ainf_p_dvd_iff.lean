-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_p_dvd_iff
-- name    : Reformulated.AutPerF.Ainf.p_dvd_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:48.183194+00:00
-- url     : https://prove2.me/theorems/ab35b253-21d2-46b7-b598-10c3e600aa79
-- title:
--   Ainf: p dvd iff
-- statement:
--   The Ainf construction uses the p dvd iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L200-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L200-L202

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

theorem Reformulated.AutPerF.Ainf.p_dvd_iff (x : Ainf p R) : (p : Ainf p R) ∣ x ↔ x.coeff 0 = 0 := by sorry
