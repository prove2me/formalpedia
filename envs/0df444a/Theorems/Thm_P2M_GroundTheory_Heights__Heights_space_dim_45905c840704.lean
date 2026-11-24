-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_space_dim_45905c840704
-- name    : P2M_GroundTheory_Heights__Heights_space_dim_45905c840704
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:44.028948+00:00
-- url     : https://prove2.me/theorems/f54ec10f-d792-45fe-8ebe-d4a74d40959d
-- title:
--   P2 M Ground Theory Heights  Heights space dim 45905c840704: P2 M Ground Theory Heights  Heights space dim 45905c840704
-- statement:
--   The P2 M Ground Theory Heights  Heights space dim 45905c840704 construction uses the P2 M Ground Theory Heights  Heights space dim 45905c840704 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L193-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L193-L197

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

theorem P2M_GroundTheory_Heights__Heights_space_dim_45905c840704 (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin n) ℂ))) = (n : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«space_dim» := P2M_GroundTheory_Heights__Heights_space_dim_45905c840704
