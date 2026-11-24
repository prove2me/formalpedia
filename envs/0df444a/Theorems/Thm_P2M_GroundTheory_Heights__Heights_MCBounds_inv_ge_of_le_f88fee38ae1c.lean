-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_inv_ge_of_le_f88fee38ae1c
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_inv_ge_of_le_f88fee38ae1c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:07.237073+00:00
-- url     : https://prove2.me/theorems/1cb8e804-777e-4202-96b8-d0bbbe4a2c82
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds inv ge of le f88fee38ae1c: P2 M Ground Theory Heights  Heights MCBounds inv ge of le f88fee38ae1c
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds inv ge of le f88fee38ae1c construction uses the P2 M Ground Theory Heights  Heights MCBounds inv ge of le f88fee38ae1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L126-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L126-L153

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MCBounds_inv_ge_of_le_f88fee38ae1c {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {l : ℝ}
    (hl : 0 < l) (hA : A.PosDef) (h : (l • (1 : Matrix ι ι ℝ) - A).PosSemidef) :
    (A⁻¹ - l⁻¹ • (1 : Matrix ι ι ℝ)).PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«inv_ge_of_le» := P2M_GroundTheory_Heights__Heights_MCBounds_inv_ge_of_le_f88fee38ae1c
