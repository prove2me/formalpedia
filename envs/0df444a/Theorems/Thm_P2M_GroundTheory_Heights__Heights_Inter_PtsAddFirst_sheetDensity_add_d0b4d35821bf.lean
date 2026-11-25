-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_sheetDensity_add_d0b4d35821bf
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_sheetDensity_add_d0b4d35821bf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:43:10.785878+00:00
-- url     : https://prove2.me/theorems/a4b032e7-1a89-4c95-b94b-1719c8be7fe4
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pts Add First sheet Density add d0b4d35821bf: P2 M Ground Theory Heights  Heights Inter Pts Add First sheet Density add d0b4d35821bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pts Add First sheet Density add d0b4d35821bf construction uses the P2 M Ground Theory Heights  Heights Inter Pts Add First sheet Density add d0b4d35821bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAddFirst.lean#L60-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAddFirst.lean#L60-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_sheetDensity_add_d0b4d35821bf {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {e : ℕ} (Q : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ))
    (L : Fin e → HermLine ι) (M N : HermLine ι) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin (e + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity Q Ψ (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) g y w =
      sheetDensity Q Ψ (Fin.cons (fun z => Real.log (M.h z)) (pot L)) g y w +
        sheetDensity Q Ψ (Fin.cons (fun z => Real.log (N.h z)) (pot L)) g y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PtsAddFirst».«sheetDensity_add» := P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_sheetDensity_add_d0b4d35821bf
