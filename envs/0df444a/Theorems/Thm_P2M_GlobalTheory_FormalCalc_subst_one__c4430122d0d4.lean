-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_one__c4430122d0d4
-- name    : P2M_GlobalTheory_FormalCalc_subst_one__c4430122d0d4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:23.94626+00:00
-- url     : https://prove2.me/theorems/a7cd7675-ad07-4e1d-a03c-fef6c72232b7
-- title:
--   P2 M Global Theory Formal Calc subst one  c4430122d0d4: P2 M Global Theory Formal Calc subst one  c4430122d0d4
-- statement:
--   The P2 M Global Theory Formal Calc subst one  c4430122d0d4 construction uses the P2 M Global Theory Formal Calc subst one  c4430122d0d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L15-L17

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

theorem P2M_GlobalTheory_FormalCalc_subst_one__c4430122d0d4 {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    subst a (1 : MvPowerSeries σ R) = 1 := by sorry

alias «GlobalTheory».«FormalCalc».«subst_one'» := P2M_GlobalTheory_FormalCalc_subst_one__c4430122d0d4
