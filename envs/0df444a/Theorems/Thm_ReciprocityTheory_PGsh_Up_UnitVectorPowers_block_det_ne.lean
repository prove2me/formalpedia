-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_block_det_ne
-- name    : ReciprocityTheory.PGsh.Up.UnitVectorPowers.block_det_ne
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:08:42.437971+00:00
-- url     : https://prove2.me/theorems/0a40fccb-a6af-4d97-b2bd-75295facdf50
-- title:
--   Unit Vector Powers: block det ne
-- statement:
--   The Unit Vector Powers construction uses the block det ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FormMonomialUnitVector.lean#L120-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FormMonomialUnitVector.lean#L120-L151

import Definitions.Def_ReciprocityTheory_DualLattices_ProdPowUnitVectorVal
import Definitions.Def_ReciprocityTheory_DualLattices_FormMonomialUnitVector
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
variable [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]

theorem ReciprocityTheory.PGsh.Up.UnitVectorPowers.block_det_ne (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (i : Fin U.m) (e : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i}) :
    (Matrix.of fun j l : {j // D.κ j = i} => Mk D j.1 (e l).1).det ≠ 0 := by sorry
