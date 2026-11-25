-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_iInf_span_xi_pow
-- name    : Reformulated.AutPerF.Ainf.iInf_span_xi_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:32:16.5562+00:00
-- url     : https://prove2.me/theorems/96624baf-d120-59d3-89c6-305c0d0ab7f5
-- title:
--   Ainf: i Inf span xi pow
-- statement:
--   The Ainf construction uses the i Inf span xi pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L347-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L347-L352

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
variable [CharZero R]

theorem Reformulated.AutPerF.Ainf.iInf_span_xi_pow (ϖ : PFlat p R) : ⨅ n : ℕ, span {xi ϖ} ^ n = ⊥ := by sorry
