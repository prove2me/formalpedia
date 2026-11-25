-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AinfInv_kerTheta_fg
-- name    : Reformulated.AutPerF.AinfInv.kerTheta_fg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:10:09.269437+00:00
-- url     : https://prove2.me/theorems/30eb2c07-62c0-4276-802a-51b178e4e3ad
-- title:
--   Ainf Inv: ker Theta fg
-- statement:
--   The Ainf Inv construction uses the ker Theta fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L501-L504
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L501-L504

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

theorem Reformulated.AutPerF.AinfInv.kerTheta_fg [IsAlgClosed (FractionRing R)] : (kerTheta p R).FG := by sorry
