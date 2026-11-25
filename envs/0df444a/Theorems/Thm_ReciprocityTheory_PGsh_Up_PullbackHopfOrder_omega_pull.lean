-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_PullbackHopfOrder_omega_pull
-- name    : ReciprocityTheory.PGsh.Up.PullbackHopfOrder.omega_pull
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:08.594211+00:00
-- url     : https://prove2.me/theorems/dd174c0e-c6fc-4a3e-aaa1-ee413f06f096
-- title:
--   Pullback Hopf Order: omega pull
-- statement:
--   The Pullback Hopf Order construction uses the omega pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemAugIdeal.lean#L74-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemAugIdeal.lean#L74-L147

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_MemAugIdeal
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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.PullbackHopfOrder
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X N : Type} [AddCommGroup X] [AddCommGroup N]

theorem ReciprocityTheory.PGsh.Up.PullbackHopfOrder.omega_pull (q : ℕ) {g d : ℕ} (ψ : X →+ N) (χ : N →+ X) (hχψ : ∀ x, χ (ψ x) = x)
    (A : Submodule R (N → C)) (hA : ∀ f ∈ A, (fun n => f (ψ (χ n))) ∈ A)
    (φ : augIdeal A →ₗ[R] LieDualModP q R g) (hsurj : Function.Surjective φ)
    (hker : LinearMap.ker φ = (sqIdeal (augIdeal A)).comap (augIdeal A).subtype)
    (F : Matrix (Fin g) (Fin g) R) (P1 : Matrix (Fin g) (Fin d) R) (P2 : Matrix (Fin d) (Fin g) R)
    (hF : P1 * P2 = F) (h21 : P2 * P1 = 1)
    (hlin : ∀ (f f' : augIdeal A) (l : Fin g → R),
      (∀ n, (f' : N → C) n = (f : N → C) (ψ (χ n))) →
      φ f = Submodule.Quotient.mk l → φ f' = Submodule.Quotient.mk (F *ᵥ l)) :
    Nonempty (OmAA (A.map (LinearMap.funLeft R C ψ)) ≃ₗ[R] LieDualModP q R d) := by sorry
