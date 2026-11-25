-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_pullDeg_add_cba51636beee
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_pullDeg_add_cba51636beee
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:39.377052+00:00
-- url     : https://prove2.me/theorems/4f557540-172b-472c-8b81-18762dcf8456
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Pullback pull Deg add cba51636beee: P2 M Ground Theory Heights  Heights Inter Diagonal Pullback pull Deg add cba51636beee
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Pullback pull Deg add cba51636beee construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Pullback pull Deg add cba51636beee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPullI.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPullI.lean#L16-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPullI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 DiagRAux
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagonalPullback

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_pullDeg_add_cba51636beee (j : Fin 2) (a b : T.YBlk → ℤ) :
    I1.pullDeg (diagonalBlockIndex j) (a + b) = I1.pullDeg (diagonalBlockIndex j) a + I1.pullDeg (diagonalBlockIndex j) b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalPullback».«pullDeg_add» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_pullDeg_add_cba51636beee
