-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_coord_le_93e1a2c1b1f2
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_coord_le_93e1a2c1b1f2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:34.619818+00:00
-- url     : https://prove2.me/theorems/aebbdb01-830d-4be8-a925-19ef096f7544
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm li exists coord le 93e1a2c1b1f2: P2 M Ground Theory Heights  Heights Herm Norm li exists coord le 93e1a2c1b1f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm li exists coord le 93e1a2c1b1f2 construction uses the P2 M Ground Theory Heights  Heights Herm Norm li exists coord le 93e1a2c1b1f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L43-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L43-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.HermNorm
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_coord_le_93e1a2c1b1f2 (h : HermNorm n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«li_exists_coord_le» := P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_coord_le_93e1a2c1b1f2
