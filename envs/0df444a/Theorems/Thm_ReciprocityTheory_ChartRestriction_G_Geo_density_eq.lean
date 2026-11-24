-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_density_eq
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.density_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:51.16646+00:00
-- url     : https://prove2.me/theorems/705a3259-69c3-4ff0-aaae-cea75f89d94e
-- title:
--   Geo: density eq
-- statement:
--   The Geo construction uses the density eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheet.lean#L33-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheet.lean#L33-L104

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Metric Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.density_eq {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {A : HermLine ι}
    {s : MRing ι} {P : Ideal (MRing ι)} (hs : IsSectionOn P A s)
    {γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (hγ : AnalyticAt ℂ γ y) (hγ' : AnalyticAt ℂ γ' y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0)
    (hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y')) :
    logNorm A s (γ y) * maDensity (fun j y' => pot L j (γ y')) y =
      logNorm A s (γ' y) * maDensity (fun j y' => pot L j (γ' y')) y := by sorry
