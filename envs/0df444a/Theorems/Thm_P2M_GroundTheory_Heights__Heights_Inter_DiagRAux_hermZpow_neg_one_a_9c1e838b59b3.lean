-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_hermZpow_neg_one_a_9c1e838b59b3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_hermZpow_neg_one_a_9c1e838b59b3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:08.712737+00:00
-- url     : https://prove2.me/theorems/db0bdd00-4ed5-4278-bf37-41ab64edead6
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux herm Zpow neg one a 9c1e838b59b3: P2 M Ground Theory Heights  Heights Inter Diag RAux herm Zpow neg one a 9c1e838b59b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux herm Zpow neg one a 9c1e838b59b3 construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux herm Zpow neg one a 9c1e838b59b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L132-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L132-L133

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_hermZpow_neg_one_a_9c1e838b59b3 (A : HermLine ι) : (hermZpow A (-1)).a = -A.a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«hermZpow_neg_one_a» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_hermZpow_neg_one_a_9c1e838b59b3
