-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_res
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.tr_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:26.916613+00:00
-- url     : https://prove2.me/theorems/2616c674-0556-4a3c-9ca8-43cfd50a5591
-- title:
--   DVR: tr res
-- statement:
--   The DVR construction uses the tr res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L100-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L100-L102

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
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
open scoped Classical
variable {X Y : Scheme.{0}} (L : LB X)

theorem ReciprocityTheory.ChartRestriction.G.DVR.tr_res {V V' : Y.Opens} (hV : V' ≤ V) {ψ : Y ⟶ X} {a b : L.ι} (h : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b)) :
    res hV (tr L V ψ a b) = tr L V' ψ a b := by sorry
