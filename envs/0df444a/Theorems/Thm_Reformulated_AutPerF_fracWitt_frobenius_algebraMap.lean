-- Prove2me | Theorems.Thm_Reformulated_AutPerF_fracWitt_frobenius_algebraMap
-- name    : Reformulated.AutPerF.fracWitt_frobenius_algebraMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:03:39.988935+00:00
-- url     : https://prove2.me/theorems/d52be9ab-8462-496b-8f9d-a5ce46b2b8ca
-- title:
--   Aut Per F: frac Witt frobenius algebra Map
-- statement:
--   The Aut Per F construction uses the frac Witt frobenius algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Coefficients.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Coefficients.lean#L37-L41

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Coefficients
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
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]
variable {p}

theorem Reformulated.AutPerF.fracWitt_frobenius_algebraMap (a : WittVector p k) :
    WittVector.FractionRing.frobenius p k (algebraMap _ _ a) =
      algebraMap _ _ (WittVector.frobenius a) := by sorry
