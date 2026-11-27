-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AinfInv_comap_kerTheta_pow
-- name    : Reformulated.AutPerF.AinfInv.comap_kerTheta_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:32:44.552922+00:00
-- url     : https://prove2.me/theorems/211c8e6f-6f14-4c57-a220-3f48a658afb7
-- title:
--   Ainf Inv: comap ker Theta pow
-- statement:
--   The Ainf Inv construction uses the comap ker Theta pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L487-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L487-L491

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
open Reformulated.AutPerF.AinfInv
variable [IsDomain R]
variable [ValuationRing R]
variable [CharZero R]

theorem Reformulated.AutPerF.AinfInv.comap_kerTheta_pow (ϖ : PFlat p R) (n : ℕ) :
    (kerTheta p R ^ n).comap (algebraMap (Ainf p R) (AinfInv p R)) = span {Ainf.xi ϖ} ^ n := by sorry
