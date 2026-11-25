-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_liftFracWitt
-- name    : Reformulated.AutPerF.AinfInv.theta_liftFracWitt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:10:12.241886+00:00
-- url     : https://prove2.me/theorems/38fbc17b-d206-44ac-8a72-19213a274bcc
-- title:
--   Ainf Inv: theta lift Frac Witt
-- statement:
--   The Ainf Inv construction uses the theta lift Frac Witt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L159-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L159-L162

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
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]
variable {p}

theorem Reformulated.AutPerF.AinfInv.theta_liftFracWitt [IsAdicComplete (span {(p : R)}) R] (g : WittVector p k →+* R)
    (a : WittVector p k) :
    AinfInv.theta p R (AinfInv.liftFracWitt p g (algebraMap _ _ a)) = algebraMap R _ (g a) := by sorry
