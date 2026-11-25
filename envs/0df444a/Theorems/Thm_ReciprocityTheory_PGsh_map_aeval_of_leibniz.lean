-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_map_aeval_of_leibniz
-- name    : ReciprocityTheory.PGsh.map_aeval_of_leibniz
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:28.654662+00:00
-- url     : https://prove2.me/theorems/c5986c68-4e70-4146-a38a-c597e94840cb
-- title:
--   PGsh: map aeval of leibniz
-- statement:
--   The PGsh construction uses the map aeval of leibniz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L83-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L83-L109

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
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem ReciprocityTheory.PGsh.map_aeval_of_leibniz {d : ℕ} (D : A →ₗ[R] A) (hD : ∀ f g, D (f * g) = f * D g + g * D f)
    (x : Fin d → A) (P : MvPolynomial (Fin d) R) :
    D (aeval x P) = ∑ j, aeval x (pderiv j P) * D (x j) := by sorry
