-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_surjective_of_frobenius
-- name    : Reformulated.AutPerF.AinfInv.theta_surjective_of_frobenius
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:29.902796+00:00
-- url     : https://prove2.me/theorems/e370f0db-c5f0-4c8a-abae-cc74b278db04
-- title:
--   Ainf Inv: theta surjective of frobenius
-- statement:
--   The Ainf Inv construction uses the theta surjective of frobenius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L298-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L298-L310

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

theorem Reformulated.AutPerF.AinfInv.theta_surjective_of_frobenius
    (hF : Function.Surjective (frobenius (ModP R p) p)) :
    Function.Surjective (AinfInv.theta p R) := by sorry
