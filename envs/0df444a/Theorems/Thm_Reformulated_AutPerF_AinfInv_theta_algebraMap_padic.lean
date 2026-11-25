-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_algebraMap_padic
-- name    : Reformulated.AutPerF.AinfInv.theta_algebraMap_padic
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:54.794382+00:00
-- url     : https://prove2.me/theorems/55b00e78-cdb7-5465-9571-68df47440da0
-- title:
--   Ainf Inv: theta algebra Map padic
-- statement:
--   The Ainf Inv construction uses the theta algebra Map padic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L183-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L183-L190

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

theorem Reformulated.AutPerF.AinfInv.theta_algebraMap_padic (g : ℤ_[p] →+* R) (j : ℚ_[p] →+* Localization.Away (p : R))
    (hj : ∀ a : ℤ_[p], j (algebraMap _ _ a) = algebraMap R _ (g a)) (x : ℚ_[p]) :
    AinfInv.theta p R (algebraMap ℚ_[p] _ x) = j x := by sorry
