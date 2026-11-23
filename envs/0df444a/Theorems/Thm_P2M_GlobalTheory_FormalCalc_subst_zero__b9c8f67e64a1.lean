-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_zero__b9c8f67e64a1
-- name    : P2M_GlobalTheory_FormalCalc_subst_zero__b9c8f67e64a1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:12.170598+00:00
-- url     : https://prove2.me/theorems/8b810bfc-b004-4af1-93e1-9072882b169f
-- title:
--   P2 M Global Theory Formal Calc subst zero  b9c8f67e64a1: P2 M Global Theory Formal Calc subst zero  b9c8f67e64a1
-- statement:
--   The P2 M Global Theory Formal Calc subst zero  b9c8f67e64a1 construction uses the P2 M Global Theory Formal Calc subst zero  b9c8f67e64a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L11-L13

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

theorem P2M_GlobalTheory_FormalCalc_subst_zero__b9c8f67e64a1 {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    subst a (0 : MvPowerSeries σ R) = 0 := by sorry

alias «GlobalTheory».«FormalCalc».«subst_zero'» := P2M_GlobalTheory_FormalCalc_subst_zero__b9c8f67e64a1
