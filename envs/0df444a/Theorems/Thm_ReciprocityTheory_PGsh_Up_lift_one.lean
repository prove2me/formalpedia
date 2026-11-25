-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_lift_one
-- name    : ReciprocityTheory.PGsh.Up.lift_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:19.86981+00:00
-- url     : https://prove2.me/theorems/6c078ddb-8e5c-47f9-a0e6-00b85776a117
-- title:
--   Up: lift one
-- statement:
--   The Up construction uses the lift one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AvgFZero.lean#L225-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AvgFZero.lean#L225-L369

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsReductionOfCoordinateCombination
import Definitions.Def_ReciprocityTheory_DualLattices_AvgFZero
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
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)

theorem ReciprocityTheory.PGsh.Up.lift_one (hS : HodgeTateSetting p v R O σ cp) (hp2 : p ≠ 2) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    (hsep : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1)
    (hcardG : IsUnit (Fintype.card G : R)) {i : Fin U.m} (hi : U.εT i ≠ 0)
    (hnt : ∃ γ, v (algebraMap R C (U.sg i (β γ) - 1)) = 1) (e : R) (lam : Ix g → R)
    (hdiv : ∃ c, cp = e * c) (wH wB : Fin g → R)
    (hrow : (wH ᵥ* H.Ht + wB ᵥ* H.Bt) ᵥ* U.εT i = e • lam) :
    ∃ u : Nb p g → C, (∀ y, v (u y) ≤ 1) ∧
      (∀ y, v (u y - algebraMap R C (∑ k, lam k * ((y k).val : R))) < 1) ∧
      (fun y => algebraMap R C e * u y) ∈ augIdeal H.AA.carrier ∧
      (∀ δ t, u (red p g (H.ρ (β δ) *ᵥ t)) = algebraMap R C (U.sg i (β δ)) * u (red p g t)) := by sorry
