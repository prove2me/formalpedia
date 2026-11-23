-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_C__c5547c7a475b
-- name    : P2M_GlobalTheory_FormalCalc_subst_C__c5547c7a475b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:28.724357+00:00
-- url     : https://prove2.me/theorems/6635a389-fc3c-40da-ba9a-53d990392654
-- title:
--   P2 M Global Theory Formal Calc subst C  c5547c7a475b: P2 M Global Theory Formal Calc subst C  c5547c7a475b
-- statement:
--   The P2 M Global Theory Formal Calc subst C  c5547c7a475b construction uses the P2 M Global Theory Formal Calc subst C  c5547c7a475b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L28-L31

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

theorem P2M_GlobalTheory_FormalCalc_subst_C__c5547c7a475b {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (r : R) :
    subst a (C r : MvPowerSeries σ R) = C (algebraMap R S r) := by sorry

alias «GlobalTheory».«FormalCalc».«subst_C'» := P2M_GlobalTheory_FormalCalc_subst_C__c5547c7a475b
