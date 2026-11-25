-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_inverseDifferent_multiple_c74a4c4152c8
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_inverseDifferent_multiple_c74a4c4152c8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:56:31.113852+00:00
-- url     : https://prove2.me/theorems/375acbc2-63e7-517a-bd03-57541483995f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume inverse Different multiple c74a4c4152c8: P2 M Ground Theory Heights  Heights Finite Covolume inverse Different multiple c74a4c4152c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume inverse Different multiple c74a4c4152c8 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume inverse Different multiple c74a4c4152c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDualLatticeMultiple.lean#L10-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDualLatticeMultiple.lean#L10-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StDualLatticeMultiple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDualLatticeMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_inverseDifferent_multiple_c74a4c4152c8 (E : Type*) [Field E] [NumberField E] :
    ∃ δ : ℤ, δ ≠ 0 ∧ ∀ z : E, (∀ a : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((a : E) * z) = n) →
      IsIntegral ℤ ((δ : E) * z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«inverseDifferent_multiple» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_inverseDifferent_multiple_c74a4c4152c8
