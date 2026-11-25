-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_phi_x_grade
-- name    : ReciprocityTheory.PGsh.Up.phi_x_grade
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:02.966727+00:00
-- url     : https://prove2.me/theorems/2cb174f3-d1e6-4b85-b5b2-7e4ff337ef34
-- title:
--   Up: phi x grade
-- statement:
--   The Up construction uses the phi x grade property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulVecMemPP.lean#L51-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulVecMemPP.lean#L51-L84

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

theorem ReciprocityTheory.PGsh.Up.phi_x_grade (hS : HodgeTateSetting p v R O σ cp) (D : Lifts H U X) (k : Ix g) (τ : Fin U.m)
    (hτ : τ ≠ D.κ k) (l : Fin g → R)
    (hl : H.φ ⟨xL D k, D.x_mem k⟩ = Submodule.Quotient.mk l) :
    (U.εL τ)ᵀ *ᵥ l ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin g → R)) := by sorry
