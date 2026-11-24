-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_comp
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.fsum_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:13:34.608963+00:00
-- url     : https://prove2.me/theorems/06bd5f8f-1c85-4fed-9b3c-16d4caccc6b8
-- title:
--   DVR: fsum comp
-- statement:
--   The DVR construction uses the fsum comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L497-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L497-L499

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
variable {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.DVR.fsum_comp (φ : K → (Y ⟶ X)) (ε : K → ℤ) {Z : Scheme.{0}} (h : Z ⟶ Y) :
    fsum (fun k => h ≫ φ k) ε = Finsupp.mapDomain (fun ψ => h ≫ ψ) (fsum φ ε) := by sorry
