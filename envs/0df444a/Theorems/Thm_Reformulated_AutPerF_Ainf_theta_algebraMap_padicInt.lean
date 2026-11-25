-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_theta_algebraMap_padicInt
-- name    : Reformulated.AutPerF.Ainf.theta_algebraMap_padicInt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:11:24.954802+00:00
-- url     : https://prove2.me/theorems/bae26d5c-787b-4125-95ee-62d8d7cc2a38
-- title:
--   Ainf: theta algebra Map padic Int
-- statement:
--   The Ainf construction uses the theta algebra Map padic Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L170-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L170-L179

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
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
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable [IsAdicComplete (span {(p : R)}) R]
variable {p}

theorem Reformulated.AutPerF.Ainf.theta_algebraMap_padicInt (g : ℤ_[p] →+* R) (a : ℤ_[p]) :
    Ainf.theta p R (algebraMap ℤ_[p] _ a) = g a := by sorry
