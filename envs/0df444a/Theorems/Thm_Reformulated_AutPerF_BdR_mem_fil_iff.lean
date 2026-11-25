-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdR_mem_fil_iff
-- name    : Reformulated.AutPerF.BdR.mem_fil_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:13:26.339722+00:00
-- url     : https://prove2.me/theorems/dc2ba5aa-0994-410a-b3e7-8d2bb3a4cce9
-- title:
--   Bd R: mem fil iff
-- statement:
--   The Bd R construction uses the mem fil iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L297-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L297-L300

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
open Reformulated.AutPerF.BdR
variable [IsAlgClosed (FractionRing R)]
variable {π : BdRPlus p R} (hπ : RingHom.ker (BdRPlus.theta p R) = span {π})
include hπ

theorem Reformulated.AutPerF.BdR.mem_fil_iff (i : ℤ) (x : BdR p R) : x ∈ fil p R i ↔ ∃ c : BdRPlus p R,
    x = algebraMap (BdRPlus p R) (BdR p R) π ^ i * algebraMap (BdRPlus p R) (BdR p R) c := by sorry
