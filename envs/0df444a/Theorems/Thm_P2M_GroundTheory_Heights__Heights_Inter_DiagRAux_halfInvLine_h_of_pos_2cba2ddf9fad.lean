-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_halfInvLine_h_of_pos_2cba2ddf9fad
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_halfInvLine_h_of_pos_2cba2ddf9fad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:56.929122+00:00
-- url     : https://prove2.me/theorems/6188cb06-dc63-4606-95d3-9607ede0aea5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux half Inv Line h of pos 2cba2ddf9fad: P2 M Ground Theory Heights  Heights Inter Diag RAux half Inv Line h of pos 2cba2ddf9fad
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux half Inv Line h of pos 2cba2ddf9fad construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux half Inv Line h of pos 2cba2ddf9fad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L106-L109

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_halfInvLine_h_of_pos_2cba2ddf9fad (A B : HermLine ι) (c : K → ℤ) (hc : ∀ k, 2 * c k = -(A.a k + B.a k))
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (halfInvLine A B c hc).h z = (A.h z * B.h z) ^ (-(1 / 2 : ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«halfInvLine_h_of_pos» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_halfInvLine_h_of_pos_2cba2ddf9fad
