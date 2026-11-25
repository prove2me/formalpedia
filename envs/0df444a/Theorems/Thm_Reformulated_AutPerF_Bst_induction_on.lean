-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Bst_induction_on
-- name    : Reformulated.AutPerF.Bst.induction_on
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:43.66775+00:00
-- url     : https://prove2.me/theorems/ab6deb43-9dfa-5c4b-92e6-ce52698af086
-- title:
--   Bst: induction on
-- statement:
--   The Bst construction uses the induction on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/ExistsFactorialMulEqPow.lean#L477-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/ExistsFactorialMulEqPow.lean#L477-L484

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

theorem Reformulated.AutPerF.Bst.induction_on {P : Bst p R → Prop} (x : Bst p R)
    (h₁ : ∀ a : Bcris p R, P (algebraMap _ _ a)) (h₂ : ∀ x y, P x → P y → P (x + y))
    (h₃ : ∀ x ϖ, P x → P (x * logFlat ϖ)) : P x := by sorry
