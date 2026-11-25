-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_mulVec_mem_pP
-- name    : ReciprocityTheory.PGsh.Up.mulVec_mem_pP
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:24:00.17834+00:00
-- url     : https://prove2.me/theorems/9902dd48-0ee4-563b-8f3e-99c7476dbdf8
-- title:
--   Up: mul Vec mem p P
-- statement:
--   The Up construction uses the mul Vec mem p P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulVecMemPP.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulVecMemPP.lean#L34-L38

import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
import Definitions.Def_ReciprocityTheory_DualLattices_MulVecMemPP
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
omit [Fact p.Prime]

theorem ReciprocityTheory.PGsh.Up.mulVec_mem_pP {n n' : ℕ} (M : Matrix (Fin n') (Fin n) R) {w : Fin n → R}
    (hw : w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n → R))) :
    M *ᵥ w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n' → R)) := by sorry
