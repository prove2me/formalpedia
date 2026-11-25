-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Bst_frob_algebraMap_padic
-- name    : Reformulated.AutPerF.Bst.frob_algebraMap_padic
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:51:48.413798+00:00
-- url     : https://prove2.me/theorems/4b33103d-f868-44fc-b38d-ad6f0ab7259b
-- title:
--   Bst: frob algebra Map padic
-- statement:
--   The Bst construction uses the frob algebra Map padic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/ExistsFactorialMulEqPow.lean#L453-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/ExistsFactorialMulEqPow.lean#L453-L456

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
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
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]
variable {p}
open Reformulated.AutPerF.Bst

theorem Reformulated.AutPerF.Bst.frob_algebraMap_padic (a : ℚ_[p]) :
    frob p R (algebraMap _ _ a) = algebraMap _ _ a := by sorry
