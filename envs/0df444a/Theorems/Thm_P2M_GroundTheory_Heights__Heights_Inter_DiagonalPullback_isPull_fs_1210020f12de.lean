-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_isPull_fs_1210020f12de
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_isPull_fs_1210020f12de
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:14.16856+00:00
-- url     : https://prove2.me/theorems/19a479a2-07e7-4f00-9b17-5a339f2b3577
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Pullback is Pull fs 1210020f12de: P2 M Ground Theory Heights  Heights Inter Diagonal Pullback is Pull fs 1210020f12de
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Pullback is Pull fs 1210020f12de construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Pullback is Pull fs 1210020f12de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPullI.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPullI.lean#L38-L48

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
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_isPull_fs_1210020f12de (j : Fin 2) (c : T.YBlk → ℤ) :
    IsPullHerm (diagonalBlockIndex j) (T.yyEmb (ι := ι) (ν := ν) (κ := κ) j)
      (HermLine.ofMetrics (fun k => fsMetric (T.yyIdx ι ν κ k)) c)
      (HermLine.ofMetrics (fun k => fsMetric (T.wwIdx ι ν κ k)) (I1.pullDeg (diagonalBlockIndex j) c)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalPullback».«isPull_fs» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_isPull_fs_1210020f12de
