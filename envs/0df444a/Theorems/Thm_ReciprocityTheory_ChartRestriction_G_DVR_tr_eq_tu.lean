-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_eq_tu
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.tr_eq_tu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:47:57.197409+00:00
-- url     : https://prove2.me/theorems/1612914d-1421-4564-9370-2470789c28ab
-- title:
--   DVR: tr eq tu
-- statement:
--   The DVR construction uses the tr eq tu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L68-L69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} (L : LB X)

theorem ReciprocityTheory.ChartRestriction.G.DVR.tr_eq_tu (V : Y.Opens) (ψ : Y ⟶ X) (a b : L.ι) :
    tr L V ψ a b = tu (fun p : L.ι × L.ι => L.U p.1 ⊓ L.U p.2) (fun p => L.g p.1 p.2) V ψ (a, b) := by sorry
