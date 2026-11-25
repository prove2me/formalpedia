-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_append_pair_eq_8bf807583c1a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_append_pair_eq_8bf807583c1a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:54.511803+00:00
-- url     : https://prove2.me/theorems/51b9ca48-7b7c-445c-a7db-4267390df28a
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux append pair eq 8bf807583c1a: P2 M Ground Theory Heights  Heights Inter Diag RAux append pair eq 8bf807583c1a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux append pair eq 8bf807583c1a construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux append pair eq 8bf807583c1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L241-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L241-L247

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
variable {α : Type*}

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_append_pair_eq_8bf807583c1a {n : ℕ} (L : Fin n → α) (A B : α) :
    (Fin.append L ![A, B] : Fin (n + 2) → α) = Fin.snoc (Fin.snoc L A : Fin (n + 1) → α) B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«append_pair_eq» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_append_pair_eq_8bf807583c1a
