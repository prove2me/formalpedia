-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_snoc_cons_comp_swap_455fd8fb2d41
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_snoc_cons_comp_swap_455fd8fb2d41
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:14.627429+00:00
-- url     : https://prove2.me/theorems/d98513da-b827-44d1-a081-9f1a93acaa8c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux snoc cons comp swap 455fd8fb2d41: P2 M Ground Theory Heights  Heights Inter Diag RAux snoc cons comp swap 455fd8fb2d41
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux snoc cons comp swap 455fd8fb2d41 construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux snoc cons comp swap 455fd8fb2d41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L224-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L224-L239

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_snoc_cons_comp_swap_455fd8fb2d41 {n : ℕ} (A B : α) (L : Fin n → α) :
    (Fin.snoc (Fin.cons A L : Fin (n + 1) → α) B : Fin (n + 2) → α) ∘ Equiv.swap 0 (Fin.last (n + 1)) =
      Fin.snoc (Fin.cons B L : Fin (n + 1) → α) A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«snoc_cons_comp_swap» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_snoc_cons_comp_swap_455fd8fb2d41
