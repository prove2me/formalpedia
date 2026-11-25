-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspShortVectors_one_le_sq_of_ne_zero_08bad7f8c873
-- name    : P2M_GroundTheory_Heights__Heights_CuspShortVectors_one_le_sq_of_ne_zero_08bad7f8c873
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:34.141421+00:00
-- url     : https://prove2.me/theorems/7d7b042d-abf8-46a8-85b9-33f40ab4eefc
-- title:
--   P2 M Ground Theory Heights  Heights Cusp Short Vectors one le sq of ne zero 08bad7f8c873: P2 M Ground Theory Heights  Heights Cusp Short Vectors one le sq of ne zero 08bad7f8c873
-- statement:
--   The P2 M Ground Theory Heights  Heights Cusp Short Vectors one le sq of ne zero 08bad7f8c873 construction uses the P2 M Ground Theory Heights  Heights Cusp Short Vectors one le sq of ne zero 08bad7f8c873 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspShortVectors.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspShortVectors.lean#L21-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspShortVectors
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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.CuspShortVectors

theorem P2M_GroundTheory_Heights__Heights_CuspShortVectors_one_le_sq_of_ne_zero_08bad7f8c873 {m : ℤ} (hm : m ≠ 0) : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CuspShortVectors».«one_le_sq_of_ne_zero» := P2M_GroundTheory_Heights__Heights_CuspShortVectors_one_le_sq_of_ne_zero_08bad7f8c873
