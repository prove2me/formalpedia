-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Acris_log_pow
-- name    : Reformulated.AutPerF.Acris.log_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:22:07.37719+00:00
-- url     : https://prove2.me/theorems/1e124293-f763-4b80-9e48-b86f9a46344c
-- title:
--   Acris: log pow
-- statement:
--   The Acris construction uses the log pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L212-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L212-L220

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
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
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Acris

theorem Reformulated.AutPerF.Acris.log_pow (u : Ainf p R) (hu : Ainf.theta p R u = 1) (m : ℕ)
    (hm : Ainf.theta p R (u ^ m) = 1) : log (u ^ m) hm = m * log u hu := by sorry
