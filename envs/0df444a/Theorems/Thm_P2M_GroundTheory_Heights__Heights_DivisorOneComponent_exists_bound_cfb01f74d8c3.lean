-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivisorOneComponent_exists_bound_cfb01f74d8c3
-- name    : P2M_GroundTheory_Heights__Heights_DivisorOneComponent_exists_bound_cfb01f74d8c3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:39:13.853643+00:00
-- url     : https://prove2.me/theorems/78f0405e-f07f-4a4f-b199-194159ecc849
-- title:
--   P2 M Ground Theory Heights  Heights Divisor One Component exists bound cfb01f74d8c3: P2 M Ground Theory Heights  Heights Divisor One Component exists bound cfb01f74d8c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Divisor One Component exists bound cfb01f74d8c3 construction uses the P2 M Ground Theory Heights  Heights Divisor One Component exists bound cfb01f74d8c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorOneComponent.lean#L24-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorOneComponent.lean#L24-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorOneComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMultGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorOneComponent
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
open MvPolynomial Filter Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.DivisorOneComponent

theorem P2M_GroundTheory_Heights__Heights_DivisorOneComponent_exists_bound_cfb01f74d8c3 (d : ℕ) : ∃ N : WithBot ℕ∞, N < (d : WithBot ℕ∞) ∧
    ∀ x : WithBot ℕ∞, x + 1 ≤ (d : WithBot ℕ∞) → x ≤ N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DivisorOneComponent».«exists_bound» := P2M_GroundTheory_Heights__Heights_DivisorOneComponent_exists_bound_cfb01f74d8c3
