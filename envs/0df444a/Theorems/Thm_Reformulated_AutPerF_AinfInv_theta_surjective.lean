-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_surjective
-- name    : Reformulated.AutPerF.AinfInv.theta_surjective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:10:03.173653+00:00
-- url     : https://prove2.me/theorems/20e40c7b-7d30-5325-942c-21880d4739b2
-- title:
--   Ainf Inv: theta surjective
-- statement:
--   The Ainf Inv construction uses the theta surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L446-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L446-L454

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

theorem Reformulated.AutPerF.AinfInv.theta_surjective [IsAlgClosed (FractionRing R)] : Function.Surjective (theta p R) := by sorry
