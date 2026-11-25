-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_exists_prime_natCast_mem_3bd80a14c2c7
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_exists_prime_natCast_mem_3bd80a14c2c7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:04:59.390971+00:00
-- url     : https://prove2.me/theorems/bd43278a-0bb8-41b9-9c51-c493a7099ec0
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements exists prime nat Cast mem 3bd80a14c2c7: P2 M Ground Theory Heights  Heights Nine Statements exists prime nat Cast mem 3bd80a14c2c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements exists prime nat Cast mem 3bd80a14c2c7 construction uses the P2 M Ground Theory Heights  Heights Nine Statements exists prime nat Cast mem 3bd80a14c2c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PNormCountBound.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PNormCountBound.lean#L12-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PNormCountBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem P2M_GroundTheory_Heights__Heights_NineStatements_exists_prime_natCast_mem_3bd80a14c2c7 {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, p.Prime ∧ (p : R) ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«exists_prime_natCast_mem» := P2M_GroundTheory_Heights__Heights_NineStatements_exists_prime_natCast_mem_3bd80a14c2c7
