-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_theta_surjective
-- name    : Reformulated.AutPerF.Ainf.theta_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:44.477592+00:00
-- url     : https://prove2.me/theorems/525b0e66-1bba-4496-9f5e-e507a526f717
-- title:
--   Ainf: theta surjective
-- statement:
--   The Ainf construction uses the theta surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L256-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L256-L259

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
open Reformulated.AutPerF.Ainf
variable [IsDomain R]
variable [ValuationRing R]

theorem Reformulated.AutPerF.Ainf.theta_surjective [IsAlgClosed (FractionRing R)] : Function.Surjective (theta p R) := by sorry
