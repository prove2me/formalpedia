-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_ptsIntegral_congr_mcPts_6069163e8079
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_ptsIntegral_congr_mcPts_6069163e8079
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:54.110102+00:00
-- url     : https://prove2.me/theorems/3f263cb5-9586-4b34-86fa-f68e04e90560
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux pts Integral congr mc Pts 6069163e8079: P2 M Ground Theory Heights  Heights Inter Diag RAux pts Integral congr mc Pts 6069163e8079
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux pts Integral congr mc Pts 6069163e8079 construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux pts Integral congr mc Pts 6069163e8079 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L37-L43

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_ptsIntegral_congr_mcPts_6069163e8079 (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hφ : ∀ j, ∀ z ∈ mcPts P, φ j z = φ' j z)
    (hg : ∀ z ∈ mcPts P, g z = g' z) : ptsIntegral P φ g = ptsIntegral P φ' g' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«ptsIntegral_congr_mcPts» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_ptsIntegral_congr_mcPts_6069163e8079
