-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sameSum_iff_fsum
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.sameSum_iff_fsum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:59.297936+00:00
-- url     : https://prove2.me/theorems/e1a983ef-62e4-47ec-9b68-6bd9dad04abb
-- title:
--   DVR: same Sum iff fsum
-- statement:
--   The DVR construction uses the same Sum iff fsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L475-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L475-L485

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.sameSum_iff_fsum (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    LB.SameSum φ ε φ' ε' ↔ fsum φ ε = fsum φ' ε' := by sorry
