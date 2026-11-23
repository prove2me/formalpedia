-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linCombIso_res
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.linCombIso_res
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:47:41.741793+00:00
-- url     : https://prove2.me/theorems/f80b5bca-36f4-4657-8816-c5791bdf7342
-- title:
--   DVR: lin Comb Iso res
-- statement:
--   The DVR construction uses the lin Comb Iso res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L86-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L86-L97

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
variable {X Y : Scheme.{0}} {L M : LB X}

theorem ReciprocityTheory.ChartRestriction.G.DVR.linCombIso_res (w : LB.Iso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (p : (LB.LinComb M φ ε).ι × (LB.LinComb L φ ε).ι) {V : Y.Opens}
    (h : V ≤ (LB.div (LB.LinComb M φ ε) (LB.LinComb L φ ε)).U p) :
    res h ((LB.linCombIso w φ ε).s p) = ∏ k, wu w V (φ k) (p.1 k) (p.2 k) ^ ε k := by sorry
