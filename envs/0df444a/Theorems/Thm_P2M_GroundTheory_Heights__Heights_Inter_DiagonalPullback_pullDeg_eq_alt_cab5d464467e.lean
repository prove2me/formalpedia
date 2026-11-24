-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_pullDeg_eq_alt_cab5d464467e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_pullDeg_eq_alt_cab5d464467e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:58.048061+00:00
-- url     : https://prove2.me/theorems/15d647f2-8ce1-410d-ba3f-21b68dd77035
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Pullback pull Deg eq alt cab5d464467e: P2 M Ground Theory Heights  Heights Inter Diagonal Pullback pull Deg eq alt cab5d464467e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Pullback pull Deg eq alt cab5d464467e construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Pullback pull Deg eq alt cab5d464467e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPullI.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPullI.lean#L24-L34

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_pullDeg_eq_alt_cab5d464467e (j : Fin 2) (c : T.YBlk → ℤ) : I1.pullDeg (diagonalBlockIndex j) c = T.pullDeg j c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalPullback».«pullDeg_eq_alt» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_pullDeg_eq_alt_cab5d464467e
