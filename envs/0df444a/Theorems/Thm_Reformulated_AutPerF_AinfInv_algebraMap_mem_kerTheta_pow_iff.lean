-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AinfInv_algebraMap_mem_kerTheta_pow_iff
-- name    : Reformulated.AutPerF.AinfInv.algebraMap_mem_kerTheta_pow_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:37.975221+00:00
-- url     : https://prove2.me/theorems/bee650a8-59fc-4413-a736-4889a16316a4
-- title:
--   Ainf Inv: algebra Map mem ker Theta pow iff
-- statement:
--   The Ainf Inv construction uses the algebra Map mem ker Theta pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L477-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L477-L485

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

theorem Reformulated.AutPerF.AinfInv.algebraMap_mem_kerTheta_pow_iff (ϖ : PFlat p R) (n : ℕ) (x : Ainf p R) :
    algebraMap (Ainf p R) (AinfInv p R) x ∈ kerTheta p R ^ n ↔ Ainf.xi ϖ ^ n ∣ x := by sorry
