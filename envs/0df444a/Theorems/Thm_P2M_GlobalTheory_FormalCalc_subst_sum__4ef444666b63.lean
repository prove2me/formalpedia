-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_sum__4ef444666b63
-- name    : P2M_GlobalTheory_FormalCalc_subst_sum__4ef444666b63
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:48.677248+00:00
-- url     : https://prove2.me/theorems/309fff42-08db-4900-9d6b-fab955144702
-- title:
--   P2 M Global Theory Formal Calc subst sum  4ef444666b63: P2 M Global Theory Formal Calc subst sum  4ef444666b63
-- statement:
--   The P2 M Global Theory Formal Calc subst sum  4ef444666b63 construction uses the P2 M Global Theory Formal Calc subst sum  4ef444666b63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L23-L26

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

theorem P2M_GlobalTheory_FormalCalc_subst_sum__4ef444666b63 {κ : Type*} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (s : Finset κ)
    (f : κ → MvPowerSeries σ R) : subst a (∑ k ∈ s, f k) = ∑ k ∈ s, subst a (f k) := by sorry

alias «GlobalTheory».«FormalCalc».«subst_sum'» := P2M_GlobalTheory_FormalCalc_subst_sum__4ef444666b63
