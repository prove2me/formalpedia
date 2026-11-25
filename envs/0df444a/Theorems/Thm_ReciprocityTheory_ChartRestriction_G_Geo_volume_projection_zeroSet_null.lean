-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_volume_projection_zeroSet_null
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.volume_projection_zeroSet_null
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:25:50.350176+00:00
-- url     : https://prove2.me/theorems/7f27ac83-9c08-468c-bb3d-bd7fee52e384
-- title:
--   Geo: volume projection zero Set null
-- statement:
--   The Geo construction uses the volume projection zero Set null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeM.lean#L53-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeM.lean#L53-L144

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.volume_projection_zeroSet_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 = 0}) = 0 := by sorry
