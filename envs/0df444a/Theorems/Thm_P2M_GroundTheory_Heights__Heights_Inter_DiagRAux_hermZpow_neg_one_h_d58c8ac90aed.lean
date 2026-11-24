-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_hermZpow_neg_one_h_d58c8ac90aed
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_hermZpow_neg_one_h_d58c8ac90aed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:09.733066+00:00
-- url     : https://prove2.me/theorems/7d2fbd2d-21c0-4dbe-9de8-23b46515736a
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux herm Zpow neg one h d58c8ac90aed: P2 M Ground Theory Heights  Heights Inter Diag RAux herm Zpow neg one h d58c8ac90aed
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux herm Zpow neg one h d58c8ac90aed construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux herm Zpow neg one h d58c8ac90aed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L129-L130

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_hermZpow_neg_one_h_d58c8ac90aed (A : HermLine ι) (z : (Σ k, ι k) → ℂ) : (hermZpow A (-1)).h z = (A.h z)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«hermZpow_neg_one_h» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_hermZpow_neg_one_h_d58c8ac90aed
