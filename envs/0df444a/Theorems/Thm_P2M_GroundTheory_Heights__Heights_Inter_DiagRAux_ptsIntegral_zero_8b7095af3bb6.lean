-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_ptsIntegral_zero_8b7095af3bb6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_ptsIntegral_zero_8b7095af3bb6
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:06.184241+00:00
-- url     : https://prove2.me/theorems/0d42e7e1-f4f2-4185-a1ae-400ab357fd7d
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux pts Integral zero 8b7095af3bb6: P2 M Ground Theory Heights  Heights Inter Diag RAux pts Integral zero 8b7095af3bb6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux pts Integral zero 8b7095af3bb6 construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux pts Integral zero 8b7095af3bb6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L45-L48

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_ptsIntegral_zero_8b7095af3bb6 (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ (fun _ => 0) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«ptsIntegral_zero» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_ptsIntegral_zero_8b7095af3bb6
