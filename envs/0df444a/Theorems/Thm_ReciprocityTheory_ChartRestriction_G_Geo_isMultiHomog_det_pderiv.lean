-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomog_det_pderiv
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_det_pderiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:22.898494+00:00
-- url     : https://prove2.me/theorems/0fef504e-ade7-495b-b3e4-dc7979ecdae2
-- title:
--   Geo: is Multi Homog det pderiv
-- statement:
--   The Geo construction uses the is Multi Homog det pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterMinor.lean#L89-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterMinor.lean#L89-L120

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinorA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinor
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
open MvPolynomial MultiHomogZ
open scoped Pointwise
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_det_pderiv {s c : ℕ} (G : Fin s → MRing ι) (hG : ∀ i, ∃ a, IsMultiHomog (G i) a)
    (a : Fin c → Fin s) (b : Fin c → Σ k, ι k) :
    ∃ d, IsMultiHomog (Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i)))) d := by sorry
