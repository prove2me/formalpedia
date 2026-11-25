-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_IsSheetParamB_sheetDensity_eq
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsSheetParamB.sheetDensity_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:13:12.890684+00:00
-- url     : https://prove2.me/theorems/05b2b7c8-cefd-40d8-af61-f5f61e73d489
-- title:
--   Is Sheet Param B: sheet Density eq
-- statement:
--   The Is Sheet Param B construction uses the sheet Density eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStBA.lean#L93-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStBA.lean#L93-L109

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStBA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Topology
open scoped ComplexOrder
variable {κ : Type} [Fintype κ] {D : ℕ}
variable {P : Ideal (MRing (GlobalTheory κ))} {Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)}
  {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → Ix κ → ℂ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsSheetParamB.sheetDensity_eq (hs : IsSheetParamB P Ψ U γ) {y : Fin D → ℂ} (hy : y ∈ U)
    (φ : Fin D → (Ix κ → ℂ) → ℝ) (h : (Ix κ → ℂ) → ℝ) :
    sheetDensity P Ψ φ h y (segre (ι := GlobalTheory κ) (γ y)) =
      h (γ y) * maDensity (fun j y' => φ j (γ y')) y := by sorry
