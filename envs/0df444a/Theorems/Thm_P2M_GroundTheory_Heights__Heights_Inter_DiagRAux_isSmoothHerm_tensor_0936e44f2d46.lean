-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_isSmoothHerm_tensor_0936e44f2d46
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_isSmoothHerm_tensor_0936e44f2d46
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:57.96362+00:00
-- url     : https://prove2.me/theorems/b0686ef2-ba17-4555-aed2-f52f5283ed90
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux is Smooth Herm tensor 0936e44f2d46: P2 M Ground Theory Heights  Heights Inter Diag RAux is Smooth Herm tensor 0936e44f2d46
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux is Smooth Herm tensor 0936e44f2d46 construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux is Smooth Herm tensor 0936e44f2d46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L118-L120

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_isSmoothHerm_tensor_0936e44f2d46 {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«isSmoothHerm_tensor» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_isSmoothHerm_tensor_0936e44f2d46
