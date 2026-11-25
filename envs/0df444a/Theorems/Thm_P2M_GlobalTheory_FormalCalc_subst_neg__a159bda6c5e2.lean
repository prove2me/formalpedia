-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_neg__a159bda6c5e2
-- name    : P2M_GlobalTheory_FormalCalc_subst_neg__a159bda6c5e2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:46.314893+00:00
-- url     : https://prove2.me/theorems/259903a8-f06f-4b58-ab2d-a7464bb4be5f
-- title:
--   P2 M Global Theory Formal Calc subst neg  a159bda6c5e2: P2 M Global Theory Formal Calc subst neg  a159bda6c5e2
-- statement:
--   The P2 M Global Theory Formal Calc subst neg  a159bda6c5e2 construction uses the P2 M Global Theory Formal Calc subst neg  a159bda6c5e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L19-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Finsupp
variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem P2M_GlobalTheory_FormalCalc_subst_neg__a159bda6c5e2 {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (f : MvPowerSeries σ R) :
    subst a (-f) = -subst a f := by sorry

alias «GlobalTheory».«FormalCalc».«subst_neg'» := P2M_GlobalTheory_FormalCalc_subst_neg__a159bda6c5e2
