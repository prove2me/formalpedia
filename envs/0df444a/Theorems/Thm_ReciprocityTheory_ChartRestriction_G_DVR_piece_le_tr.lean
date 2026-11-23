-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_piece_le_tr
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.piece_le_tr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:09.282402+00:00
-- url     : https://prove2.me/theorems/9f88313b-7493-406b-96bf-07d48cd7442d
-- title:
--   DVR: piece le tr
-- statement:
--   The DVR construction uses the piece le tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L162-L164

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
variable {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
  (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
variable {L φ φ'}

theorem ReciprocityTheory.ChartRestriction.G.DVR.piece_le_tr {j' : K' → L.ι} {V : Y.Opens} {ρ : (Y ⟶ X) → L.ι} (hV : V ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ)
    (k' : K') : V ≤ φ' k' ⁻¹ᵁ (L.U (ρ (φ' k')) ⊓ L.U (j' k')) := by sorry
