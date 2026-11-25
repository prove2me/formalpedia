-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_IsSheetParamB_isSheet
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsSheetParamB.isSheet
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:06.600802+00:00
-- url     : https://prove2.me/theorems/b81d5fad-a8d8-418c-98f1-f9a3f4a6905b
-- title:
--   Is Sheet Param B: is Sheet
-- statement:
--   The Is Sheet Param B construction uses the is Sheet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStBA.lean#L66-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStBA.lean#L66-L71

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsSheetParamB.isSheet (hs : IsSheetParamB P Ψ U γ) {y : Fin D → ℂ} (hy : y ∈ U) :
    IsSheet P Ψ y (segre (ι := GlobalTheory κ) (γ y)) γ := by sorry
