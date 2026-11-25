-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_finsum_divSupp_eq
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.finsum_divSupp_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:25:28.352749+00:00
-- url     : https://prove2.me/theorems/223bbd38-c6c1-4b43-a21b-5050f074acbc
-- title:
--   Geo: finsum div Supp eq
-- statement:
--   The Geo construction uses the finsum div Supp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushA.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushA.lean#L72-L77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
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

theorem ReciprocityTheory.ChartRestriction.G.Geo.finsum_divSupp_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (s : MRing ι) (g : Ideal (MRing ι) → ℝ) :
    (∑ᶠ (W') (_ : W' ∈ divSupp P s ∧ IsHorizontal W'), g W') =
      ∑ W' ∈ ((divSupp_finite P s).subset (fun _ h => h.1) :
        {W' | W' ∈ divSupp P s ∧ IsHorizontal W'}.Finite).toFinset, g W' := by sorry
