-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up__L_eq_zero_of_r_a5bd42719c11
-- name    : P2M_ReciprocityTheory_PGsh_Up__L_eq_zero_of_r_a5bd42719c11
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:34:27.808709+00:00
-- url     : https://prove2.me/theorems/c38892d1-f1ce-4a5b-8ec1-9e55635928f1
-- title:
--   P2 M Reciprocity Theory PGsh Up  L eq zero of r a5bd42719c11: P2 M Reciprocity Theory PGsh Up  L eq zero of r a5bd42719c11
-- statement:
--   The P2 M Reciprocity Theory PGsh Up  L eq zero of r a5bd42719c11 construction uses the P2 M Reciprocity Theory PGsh Up  L eq zero of r a5bd42719c11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulVecMemPP.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulVecMemPP.lean#L40-L49

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

theorem P2M_ReciprocityTheory_PGsh_Up__L_eq_zero_of_r_a5bd42719c11 (U : UnramData p g v R O σ cp H) {τ : Fin U.m} (h : U.r τ = 0) :
    U.εL τ = 0 := by sorry

alias «ReciprocityTheory».«PGsh».«Up».«εL_eq_zero_of_r» := P2M_ReciprocityTheory_PGsh_Up__L_eq_zero_of_r_a5bd42719c11
