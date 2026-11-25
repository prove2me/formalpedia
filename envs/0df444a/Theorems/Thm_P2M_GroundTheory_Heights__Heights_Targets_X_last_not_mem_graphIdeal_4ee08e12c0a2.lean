-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_X_last_not_mem_graphIdeal_4ee08e12c0a2
-- name    : P2M_GroundTheory_Heights__Heights_Targets_X_last_not_mem_graphIdeal_4ee08e12c0a2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:31.200799+00:00
-- url     : https://prove2.me/theorems/2e1ae7d3-fa52-4f55-8115-952e4512fd3e
-- title:
--   P2 M Ground Theory Heights  Heights Targets X last not mem graph Ideal 4ee08e12c0a2: P2 M Ground Theory Heights  Heights Targets X last not mem graph Ideal 4ee08e12c0a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets X last not mem graph Ideal 4ee08e12c0a2 construction uses the P2 M Ground Theory Heights  Heights Targets X last not mem graph Ideal 4ee08e12c0a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L96-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
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
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Targets_X_last_not_mem_graphIdeal_4ee08e12c0a2 {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : MvPolynomial (Fin n) ℂ} (hp : p ∉ J) :
    X (Fin.last n) ∉ graphIdeal J p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«X_last_not_mem_graphIdeal» := P2M_GroundTheory_Heights__Heights_Targets_X_last_not_mem_graphIdeal_4ee08e12c0a2
