-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_mk_theta
-- name    : Reformulated.AutPerF.Ainf.mk_theta
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:40.574643+00:00
-- url     : https://prove2.me/theorems/29112415-cbeb-4d8f-9e2c-3c38e16d5e19
-- title:
--   Ainf: mk theta
-- statement:
--   The Ainf construction uses the mk theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L230-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L230-L232

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

theorem Reformulated.AutPerF.Ainf.mk_theta (x : Ainf p R) : Ideal.Quotient.mk (span {(p : R)}) (theta p R x) =
    Ideal.Quotient.mk _ (PreTilt.untilt (x.coeff 0)) := by sorry
