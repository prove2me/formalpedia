-- Prove2me | Theorems.Thm_Reformulated_AutPerF_wittResidueMap_coeff_zero
-- name    : Reformulated.AutPerF.wittResidueMap_coeff_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:37.429987+00:00
-- url     : https://prove2.me/theorems/5dc3da75-12ca-4213-a314-4935d4d17c03
-- title:
--   Aut Per F: witt Residue Map coeff zero
-- statement:
--   The Aut Per F construction uses the witt Residue Map coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L69-L75

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
variable {k : Type w} [CommRing k] [CharP k p] [PerfectRing k p]
omit [Fact ¬IsUnit (p : R)]
variable {p}

theorem Reformulated.AutPerF.wittResidueMap_coeff_zero (g : WittVector p k →+* R) (x : WittVector p k) :
    wittResidueMap p g (x.coeff 0) = Ideal.Quotient.mk _ (g x) := by sorry
