-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_coeff_eq_zero_of_stable
-- name    : ReciprocityTheory.PGsh.coeff_eq_zero_of_stable
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:35.345219+00:00
-- url     : https://prove2.me/theorems/17e14eb5-73b0-4b2e-81f5-46c698fe5f56
-- title:
--   PGsh: coeff eq zero of stable
-- statement:
--   The PGsh construction uses the coeff eq zero of stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L214-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L214-L304

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {d p : ℕ}

theorem ReciprocityTheory.PGsh.coeff_eq_zero_of_stable (ε : A →ₐ[R] R) (x : Fin d → A) (hx : ∀ i, ε (x i) = 0)
    (D : Fin d → A →ₗ[R] A) (hD : ∀ i f g, D i (f * g) = f * D i g + g * D i f)
    (hDx : ∀ i j, ε (D i (x j)) = if i = j then 1 else 0)
    (hsurj : Function.Surjective (aeval (R := R) x))
    (hp0 : (p : R) = 0) (hunit : ∀ n, 0 < n → n < p → IsUnit (n : R))
    (K : Set A) (hK : ∀ a ∈ K, ε a = 0) (hKD : ∀ i, ∀ a ∈ K, D i a ∈ K)
    (P : MvPolynomial (Fin d) R) (hP : aeval x P ∈ K) :
    ∀ β : Fin d →₀ ℕ, (∀ j, β j < p) → coeff β P = 0 := by sorry
