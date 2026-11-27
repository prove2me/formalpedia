-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_fil_eq_maximalIdeal_pow
-- name    : Reformulated.AutPerF.BdRPlus.fil_eq_maximalIdeal_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:11:57.281301+00:00
-- url     : https://prove2.me/theorems/792f8a41-d888-5a08-a79a-686a5e76ffb3
-- title:
--   Bd RPlus: fil eq maximal Ideal pow
-- statement:
--   The Bd RPlus construction uses the fil eq maximal Ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L214-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L214-L215

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
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
variable [IsDomain R] [ValuationRing R] [CharZero R]
open Reformulated.AutPerF.BdRPlus
variable [IsAlgClosed (FractionRing R)]

theorem Reformulated.AutPerF.BdRPlus.fil_eq_maximalIdeal_pow (n : ℕ) :
    fil p R n = IsLocalRing.maximalIdeal (BdRPlus p R) ^ n := by sorry
