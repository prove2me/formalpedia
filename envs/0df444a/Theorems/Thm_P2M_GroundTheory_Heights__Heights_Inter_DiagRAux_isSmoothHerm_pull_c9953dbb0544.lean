-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_isSmoothHerm_pull_c9953dbb0544
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_isSmoothHerm_pull_c9953dbb0544
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:31.463267+00:00
-- url     : https://prove2.me/theorems/9cace136-0d10-42a3-8f4a-df77b22ddb3b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux is Smooth Herm pull c9953dbb0544: P2 M Ground Theory Heights  Heights Inter Diag RAux is Smooth Herm pull c9953dbb0544
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux is Smooth Herm pull c9953dbb0544 construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux is Smooth Herm pull c9953dbb0544 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L275-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L275-L291

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_isSmoothHerm_pull_c9953dbb0544 (j : Fin 2) {X : HermLine (T.yyIdx ι ν κ)} {X' : HermLine (T.wwIdx ι ν κ)}
    (hX : IsSmoothHerm X) (hp : IsPullHerm (diagonalBlockIndex j) (T.yyEmb j) X X') : IsSmoothHerm X' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«isSmoothHerm_pull» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_isSmoothHerm_pull_c9953dbb0544
