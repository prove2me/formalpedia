-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspCoordinateBound_mulVec_sq_le_9aca54dee268
-- name    : P2M_GroundTheory_Heights__Heights_CuspCoordinateBound_mulVec_sq_le_9aca54dee268
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:32:41.872159+00:00
-- url     : https://prove2.me/theorems/92a2932a-9ec5-47ac-a6ca-e94f0cef5bb8
-- title:
--   P2 M Ground Theory Heights  Heights Cusp Coordinate Bound mul Vec sq le 9aca54dee268: P2 M Ground Theory Heights  Heights Cusp Coordinate Bound mul Vec sq le 9aca54dee268
-- statement:
--   The P2 M Ground Theory Heights  Heights Cusp Coordinate Bound mul Vec sq le 9aca54dee268 construction uses the P2 M Ground Theory Heights  Heights Cusp Coordinate Bound mul Vec sq le 9aca54dee268 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspCoordinateBound.lean#L22-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspCoordinateBound.lean#L22-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspCoordinateBound
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
open GroundTheory.Heights₂.Heights.CuspCoordinateBound

theorem P2M_GroundTheory_Heights__Heights_CuspCoordinateBound_mulVec_sq_le_9aca54dee268 {g : ℕ} (X : Matrix (Fin g) (Fin g) ℝ) (M : ℝ) (k : Fin g)
    (hX : ∀ l, |X k l| ≤ M) (β : Fin g → ℝ) :
    (X *ᵥ β) k ^ 2 ≤ g * M ^ 2 * ∑ l, β l ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CuspCoordinateBound».«mulVec_sq_le» := P2M_GroundTheory_Heights__Heights_CuspCoordinateBound_mulVec_sq_le_9aca54dee268
