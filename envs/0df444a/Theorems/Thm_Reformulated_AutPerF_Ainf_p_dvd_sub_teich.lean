-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_p_dvd_sub_teich
-- name    : Reformulated.AutPerF.Ainf.p_dvd_sub_teich
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:34:55.550778+00:00
-- url     : https://prove2.me/theorems/528baf7d-d819-48a6-9187-83e3fa184267
-- title:
--   Ainf: p dvd sub teich
-- statement:
--   The Ainf construction uses the p dvd sub teich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L205-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L205-L209

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

theorem Reformulated.AutPerF.Ainf.p_dvd_sub_teich (x : Ainf p R) : (p : Ainf p R) ∣ x - teich p (x.coeff 0) := by sorry
