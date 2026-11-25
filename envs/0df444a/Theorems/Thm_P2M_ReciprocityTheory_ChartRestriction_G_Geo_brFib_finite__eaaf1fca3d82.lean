-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_brFib_finite__eaaf1fca3d82
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_brFib_finite__eaaf1fca3d82
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:17:29.551623+00:00
-- url     : https://prove2.me/theorems/7a36c1c3-6f9b-4a67-81dc-a42e92391715
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo br Fib finite  eaaf1fca3d82: P2 M Reciprocity Theory Chart Restriction G Geo br Fib finite  eaaf1fca3d82
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo br Fib finite  eaaf1fca3d82 construction uses the P2 M Reciprocity Theory Chart Restriction G Geo br Fib finite  eaaf1fca3d82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeL.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeL.lean#L14-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeL
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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_brFib_finite__eaaf1fca3d82 (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} ∩ {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0}).Finite := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«brFib_finite'» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_brFib_finite__eaaf1fca3d82
