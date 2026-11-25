-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_sheetDensity_congr_mcPts_15faba685dcb
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_sheetDensity_congr_mcPts_15faba685dcb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:28.230071+00:00
-- url     : https://prove2.me/theorems/97ab5415-1aeb-444b-a5b1-45ddebb505ef
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux sheet Density congr mc Pts 15faba685dcb: P2 M Ground Theory Heights  Heights Inter Diag RAux sheet Density congr mc Pts 15faba685dcb
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux sheet Density congr mc Pts 15faba685dcb construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux sheet Density congr mc Pts 15faba685dcb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L21-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L21-L35

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_sheetDensity_congr_mcPts_15faba685dcb (P : Ideal (MRing ι)) {e : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hφ : ∀ j, ∀ z ∈ mcPts P, φ j z = φ' j z)
    (hg : ∀ z ∈ mcPts P, g z = g' z) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ' g' y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«sheetDensity_congr_mcPts» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_sheetDensity_congr_mcPts_15faba685dcb
