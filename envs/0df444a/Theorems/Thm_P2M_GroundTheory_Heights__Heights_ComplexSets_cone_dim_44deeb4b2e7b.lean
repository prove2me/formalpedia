-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_cone_dim_44deeb4b2e7b
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_cone_dim_44deeb4b2e7b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:58.541314+00:00
-- url     : https://prove2.me/theorems/066f15c0-f031-493b-978e-c7d22e966a8b
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets cone dim 44deeb4b2e7b: P2 M Ground Theory Heights  Heights Complex Sets cone dim 44deeb4b2e7b
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets cone dim 44deeb4b2e7b construction uses the P2 M Ground Theory Heights  Heights Complex Sets cone dim 44deeb4b2e7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L191-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L191-L244

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_cone_dim_44deeb4b2e7b :
    ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«cone_dim» := P2M_GroundTheory_Heights__Heights_ComplexSets_cone_dim_44deeb4b2e7b
