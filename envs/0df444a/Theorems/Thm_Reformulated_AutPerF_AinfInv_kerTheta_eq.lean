-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AinfInv_kerTheta_eq
-- name    : Reformulated.AutPerF.AinfInv.kerTheta_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:12:02.019289+00:00
-- url     : https://prove2.me/theorems/0d737155-90d8-4513-bffd-f6c69cfd271d
-- title:
--   Ainf Inv: ker Theta eq
-- statement:
--   The Ainf Inv construction uses the ker Theta eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L464-L475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L464-L475

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

theorem Reformulated.AutPerF.AinfInv.kerTheta_eq (ϖ : PFlat p R) :
    kerTheta p R = span {algebraMap (Ainf p R) (AinfInv p R) (Ainf.xi ϖ)} := by sorry
