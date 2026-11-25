-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_smooth_cons_2fd13f6c2548
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_smooth_cons_2fd13f6c2548
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:19.297797+00:00
-- url     : https://prove2.me/theorems/ddcce6c7-a195-458e-870b-f544d22fde73
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux smooth cons 2fd13f6c2548: P2 M Ground Theory Heights  Heights Inter Diag RAux smooth cons 2fd13f6c2548
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux smooth cons 2fd13f6c2548 construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux smooth cons 2fd13f6c2548 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L255-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L255-L260

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_smooth_cons_2fd13f6c2548 {n : ℕ} {A : HermLine ι} {L : Fin n → HermLine ι} (hA : IsSmoothHerm A)
    (hL : ∀ j, IsSmoothHerm (L j)) : ∀ j, IsSmoothHerm ((Fin.cons A L : Fin (n + 1) → HermLine ι) j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«smooth_cons» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_smooth_cons_2fd13f6c2548
