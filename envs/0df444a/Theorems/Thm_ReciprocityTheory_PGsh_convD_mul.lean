-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_convD_mul
-- name    : ReciprocityTheory.PGsh.convD_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:14.387342+00:00
-- url     : https://prove2.me/theorems/283cbca0-0e0e-55c8-a326-d3bfd0f4e0fd
-- title:
--   PGsh: conv D mul
-- statement:
--   The PGsh construction uses the conv D mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L37-L44

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
variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]

theorem ReciprocityTheory.PGsh.convD_mul (δ : A →ₗ[R] R) (hδ : IsPtDer δ) (f g : A) :
    convD δ (f * g) = f * convD δ g + g * convD δ f := by sorry
