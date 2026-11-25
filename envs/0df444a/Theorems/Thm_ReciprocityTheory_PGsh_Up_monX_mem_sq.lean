-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_monX_mem_sq
-- name    : ReciprocityTheory.PGsh.Up.monX_mem_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:16:59.299353+00:00
-- url     : https://prove2.me/theorems/db52fa48-15bc-5455-b3f0-009995bbd416
-- title:
--   Up: mon X mem sq
-- statement:
--   The Up construction uses the mon X mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HasLenLeOfSurj.lean#L126-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HasLenLeOfSurj.lean#L126-L141

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

theorem ReciprocityTheory.PGsh.Up.monX_mem_sq (D : Lifts H U X) {α : Nb p g} (h0 : α ≠ 0) (h1 : ∀ k, α ≠ Pi.single k 1) :
    monX D α ∈ sqIdeal (augIdeal H.AA.carrier) := by sorry
