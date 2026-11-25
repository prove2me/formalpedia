-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_point_dim_bd96f39da953
-- name    : P2M_GroundTheory_Heights__Heights_point_dim_bd96f39da953
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:23.075893+00:00
-- url     : https://prove2.me/theorems/10ec315d-edc8-4c47-94d1-40cfa1bde180
-- title:
--   P2 M Ground Theory Heights  Heights point dim bd96f39da953: P2 M Ground Theory Heights  Heights point dim bd96f39da953
-- statement:
--   The P2 M Ground Theory Heights  Heights point dim bd96f39da953 construction uses the P2 M Ground Theory Heights  Heights point dim bd96f39da953 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L208-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L208-L214

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_point_dim_bd96f39da953 {n : ℕ} (p : Fin n → ℂ) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ RingHom.ker (MvPolynomial.eval p)) = (0 : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«point_dim» := P2M_GroundTheory_Heights__Heights_point_dim_bd96f39da953
