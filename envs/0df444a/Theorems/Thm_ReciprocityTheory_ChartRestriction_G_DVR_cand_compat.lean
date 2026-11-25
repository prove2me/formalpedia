-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cand_compat
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.cand_compat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:16.741467+00:00
-- url     : https://prove2.me/theorems/a394290c-4256-58f9-b275-1e04d11f9122
-- title:
--   DVR: cand compat
-- statement:
--   The DVR construction uses the cand compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L184-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L184-L213

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
variable (L φ φ')
variable {L φ ε φ' ε'}

theorem ReciprocityTheory.ChartRestriction.G.DVR.cand_compat (hL : L.IsLB) (hs : LB.SameSum φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (j' : K' → L.ι) (ρ ρ₂ : (Y ⟶ X) → L.ι) :
    res (inf_le_left : (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂) ≤ _)
        (cand L φ ε φ' ε' t j' ρ) =
      res (inf_le_right : (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂) ≤ _)
        (cand L φ ε φ' ε' t j' ρ₂) := by sorry
