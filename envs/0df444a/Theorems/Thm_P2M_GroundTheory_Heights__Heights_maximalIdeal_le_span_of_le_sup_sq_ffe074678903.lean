-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_maximalIdeal_le_span_of_le_sup_sq_ffe074678903
-- name    : P2M_GroundTheory_Heights__Heights_maximalIdeal_le_span_of_le_sup_sq_ffe074678903
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:50:00.985247+00:00
-- url     : https://prove2.me/theorems/c27871e8-e3d6-54e5-9d67-db4e7016b4b2
-- title:
--   P2 M Ground Theory Heights  Heights maximal Ideal le span of le sup sq ffe074678903: P2 M Ground Theory Heights  Heights maximal Ideal le span of le sup sq ffe074678903
-- statement:
--   The P2 M Ground Theory Heights  Heights maximal Ideal le span of le sup sq ffe074678903 construction uses the P2 M Ground Theory Heights  Heights maximal Ideal le span of le sup sq ffe074678903 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L133-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L133-L139

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Module
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_maximalIdeal_le_span_of_le_sup_sq_ffe074678903 {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (T : Set R)
    (h : IsLocalRing.maximalIdeal R ≤ Ideal.span T ⊔ IsLocalRing.maximalIdeal R ^ 2) :
    IsLocalRing.maximalIdeal R ≤ Ideal.span T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«maximalIdeal_le_span_of_le_sup_sq» := P2M_GroundTheory_Heights__Heights_maximalIdeal_le_span_of_le_sup_sq_ffe074678903
