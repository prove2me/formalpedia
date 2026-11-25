-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_bR_eig
-- name    : ReciprocityTheory.PGsh.Up.UnitVectorPowers.bR_eig
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:52.172036+00:00
-- url     : https://prove2.me/theorems/ceed1c4b-ff29-5f19-8cc8-ad2f341803d3
-- title:
--   Unit Vector Powers: b R eig
-- statement:
--   The Unit Vector Powers construction uses the b R eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdPowUnitVectorVal.lean#L114-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdPowUnitVectorVal.lean#L114-L135

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ProdPowUnitVectorVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.UnitVectorPowers
open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

theorem ReciprocityTheory.PGsh.Up.UnitVectorPowers.bR_eig (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j : Ix g) (k : Fin D.s) (α : Nb p g) :
    (∏ j', U.sg (D.κ j') (D.b k) ^ (α j').val) * bR hv D j α =
      U.sg (U.φ (D.κ j)) (D.b k) * bR hv D j α := by sorry
