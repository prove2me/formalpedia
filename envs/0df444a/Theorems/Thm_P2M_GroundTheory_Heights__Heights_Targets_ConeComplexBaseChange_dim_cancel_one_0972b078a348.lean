-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_dim_cancel_one_0972b078a348
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_dim_cancel_one_0972b078a348
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:56.237817+00:00
-- url     : https://prove2.me/theorems/57dc6a45-7bd1-4c36-87c9-9bf1f687a182
-- title:
--   P2 M Ground Theory Heights  Heights Targets Cone Complex Base Change dim cancel one 0972b078a348: P2 M Ground Theory Heights  Heights Targets Cone Complex Base Change dim cancel one 0972b078a348
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Cone Complex Base Change dim cancel one 0972b078a348 construction uses the P2 M Ground Theory Heights  Heights Targets Cone Complex Base Change dim cancel one 0972b078a348 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PConeComplexBaseChange.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PConeComplexBaseChange.lean#L39-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeComplexBaseChange
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PConeComplexBaseChange
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange
variable {σ : Type} [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_dim_cancel_one_0972b078a348 {d : WithBot ℕ∞} {N : ℕ} (h : d + 1 = ((N + 1 : ℕ) : WithBot ℕ∞)) :
    d = (N : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ConeComplexBaseChange».«dim_cancel_one» := P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_dim_cancel_one_0972b078a348
