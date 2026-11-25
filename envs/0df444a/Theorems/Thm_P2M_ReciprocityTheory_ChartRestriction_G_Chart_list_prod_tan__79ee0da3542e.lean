-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_list_prod_tan__79ee0da3542e
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Chart_list_prod_tan__79ee0da3542e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:09:21.725804+00:00
-- url     : https://prove2.me/theorems/a55485d3-9df8-40e1-84af-49df82291e8f
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Chart list prod tan  79ee0da3542e: P2 M Reciprocity Theory Chart Restriction G Chart list prod tan  79ee0da3542e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Chart list prod tan  79ee0da3542e construction uses the P2 M Reciprocity Theory Chart Restriction G Chart list prod tan  79ee0da3542e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L25-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L25-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {Gx : Over (Spec (CommRingCat.of R))} [GrpObj Gx] {n : ℕ}
  {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ Gx} (hx : IsUnivChart Gx n x)

theorem P2M_ReciprocityTheory_ChartRestriction_G_Chart_list_prod_tan__79ee0da3542e : ∀ {M : ℕ} (u : Fin M → (sp (R₀ := R) (DualNumber R) ⟶ Gx)) (hu : ∀ i, IsTan (u i)),
    ∃ h : IsTan (List.ofFn u).prod, tcoord hx _ h = ∑ i, tcoord hx (u i) (hu i)
  := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Chart».«list_prod_tan'» := P2M_ReciprocityTheory_ChartRestriction_G_Chart_list_prod_tan__79ee0da3542e
