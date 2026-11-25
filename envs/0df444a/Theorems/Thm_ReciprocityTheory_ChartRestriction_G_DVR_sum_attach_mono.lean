-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sum_attach_mono
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.sum_attach_mono
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:25:30.516816+00:00
-- url     : https://prove2.me/theorems/a497b674-8ac4-595c-8c12-46f2e7146316
-- title:
--   DVR: sum attach mono
-- statement:
--   The DVR construction uses the sum attach mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpIdentRestrict.lean#L45-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpIdentRestrict.lean#L45-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpIdentRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G]

theorem ReciprocityTheory.ChartRestriction.G.DVR.sum_attach_mono {X β : Type} [AddCommMonoid β] {S S' : Finset X} (hSS : S ⊆ S')
    (T : S' → β) (h0 : ∀ α : S', α.1 ∉ S → T α = 0) :
    ∑ α ∈ S'.attach, T α = ∑ α ∈ S.attach, T ⟨α.1, hSS α.2⟩ := by sorry
