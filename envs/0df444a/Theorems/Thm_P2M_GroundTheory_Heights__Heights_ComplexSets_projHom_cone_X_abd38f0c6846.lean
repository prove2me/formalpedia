-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_projHom_cone_X_abd38f0c6846
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_projHom_cone_X_abd38f0c6846
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:08.578256+00:00
-- url     : https://prove2.me/theorems/6102251c-6099-41fd-a95a-12246dfea79e
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets proj Hom cone X abd38f0c6846: P2 M Ground Theory Heights  Heights Complex Sets proj Hom cone X abd38f0c6846
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets proj Hom cone X abd38f0c6846 construction uses the P2 M Ground Theory Heights  Heights Complex Sets proj Hom cone X abd38f0c6846 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L259-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L259-L261

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_projHom_cone_X_abd38f0c6846 (i : Fin 2) :
    projHom coneIdeal coneProj (X i) = Ideal.Quotient.mk coneIdeal (X i.succ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«projHom_cone_X» := P2M_GroundTheory_Heights__Heights_ComplexSets_projHom_cone_X_abd38f0c6846
