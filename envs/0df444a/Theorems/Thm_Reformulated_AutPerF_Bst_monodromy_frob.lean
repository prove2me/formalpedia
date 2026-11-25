-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_frob
-- name    : Reformulated.AutPerF.Bst.monodromy_frob
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:38:28.71665+00:00
-- url     : https://prove2.me/theorems/ef3829a4-ed4b-4d9e-b29b-a285c805adea
-- title:
--   Bst: monodromy frob
-- statement:
--   The Bst construction uses the monodromy frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/ExistsFactorialMulEqPow.lean#L489-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/ExistsFactorialMulEqPow.lean#L489-L497

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

theorem Reformulated.AutPerF.Bst.monodromy_frob (x : Bst p R) :
    monodromy p R (frob p R x) = p * frob p R (monodromy p R x) := by sorry
