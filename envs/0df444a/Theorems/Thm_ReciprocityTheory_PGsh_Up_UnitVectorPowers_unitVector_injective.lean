-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_unitVector_injective
-- name    : ReciprocityTheory.PGsh.Up.UnitVectorPowers.unitVector_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:37.760615+00:00
-- url     : https://prove2.me/theorems/7d56bcba-ad7c-5005-a3fc-fa6fd3ef2840
-- title:
--   Unit Vector Powers: unit Vector injective
-- statement:
--   The Unit Vector Powers construction uses the unit Vector injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdPowUnitVectorVal.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdPowUnitVectorVal.lean#L38-L44

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

theorem ReciprocityTheory.PGsh.Up.UnitVectorPowers.unitVector_injective : Function.Injective (e1 (p := p) (g := g)) := by sorry
