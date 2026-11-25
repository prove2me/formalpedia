-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_locDens_chart
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.locDens_chart
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:07.562609+00:00
-- url     : https://prove2.me/theorems/e56db08a-e82c-4d35-b4f9-d2fe7cdacab3
-- title:
--   Geo: loc Dens chart
-- statement:
--   The Geo construction uses the loc Dens chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeA.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeA.lean#L21-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeI
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeJ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
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
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.ChartRestriction.G.Geo.locDens_chart (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (j k : Fin A.n) (y : Fin e → ℂ)
    (hy : y ∈ (A.chart j).target) (hk : (A.chart j).symm y ∈ (A.chart k).source) :
    locDens A Φ j y = locDens A Φ k (A.chart k ((A.chart j).symm y)) *
      ‖LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by sorry
