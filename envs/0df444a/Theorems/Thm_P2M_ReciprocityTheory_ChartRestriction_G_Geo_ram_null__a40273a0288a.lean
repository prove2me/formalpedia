-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_ram_null__a40273a0288a
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_ram_null__a40273a0288a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:17:37.251457+00:00
-- url     : https://prove2.me/theorems/8d6d2659-ab83-426b-bd1b-11192bb5a891
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo ram null  a40273a0288a: P2 M Reciprocity Theory Chart Restriction G Geo ram null  a40273a0288a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo ram null  a40273a0288a construction uses the P2 M Reciprocity Theory Chart Restriction G Geo ram null  a40273a0288a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeM.lean#L12-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeM.lean#L12-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeL
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeM
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
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e)

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_ram_null__a40273a0288a (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«ram_null'» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_ram_null__a40273a0288a
