-- Prove2me | Theorems.Thm_P2M_GlobalTheory_factorPow_eval__9207485a8623
-- name    : P2M_GlobalTheory_factorPow_eval__9207485a8623
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:38.130643+00:00
-- url     : https://prove2.me/theorems/c42a1f7e-c0f4-46aa-b187-adc815b97b50
-- title:
--   P2 M Global Theory factor Pow eval  9207485a8623: P2 M Global Theory factor Pow eval  9207485a8623
-- statement:
--   The P2 M Global Theory factor Pow eval  9207485a8623 construction uses the P2 M Global Theory factor Pow eval  9207485a8623 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L13-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {A R : Type*} [CommRing A] [CommRing R]

theorem P2M_GlobalTheory_factorPow_eval__9207485a8623 (J : Ideal A) {m n : ℕ} (h : m ≤ n) (x : AdicCompletion J A) :
    Ideal.Quotient.factorPow J h (AdicCompletion.evalₐ J n x) = AdicCompletion.evalₐ J m x := by sorry

alias «GlobalTheory».«factorPow_evalₐ» := P2M_GlobalTheory_factorPow_eval__9207485a8623
