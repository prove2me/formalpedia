-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gm_linCombIso
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.gm_linCombIso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:16.864961+00:00
-- url     : https://prove2.me/theorems/82d1b16a-9691-4de6-b09e-d48169fcd150
-- title:
--   DVR: gm lin Comb Iso
-- statement:
--   The DVR construction uses the gm lin Comb Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdExpPf.lean#L149-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdExpPf.lean#L149-L156

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem ReciprocityTheory.ChartRestriction.G.DVR.gm_linCombIso (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (r : Z ⟶ Y) (z : Z) (jN : K → Fin j → M.ι) (jM : K → M'.ι)
    (hz : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ jN ⊓ LB.wchart M' φ jM) :
    gm r z (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ jN ⊓ LB.wchart M' φ jM) ((LB.linCombIso w φ ε).s (jN, jM)) =
      ∏ a, bw w (r ≫ φ a) z (jN a) (jM a) ^ ε a := by sorry
