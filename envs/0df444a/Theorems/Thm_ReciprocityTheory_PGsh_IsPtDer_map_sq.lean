-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_IsPtDer_map_sq
-- name    : ReciprocityTheory.PGsh.IsPtDer.map_sq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:41.656961+00:00
-- url     : https://prove2.me/theorems/c02a1be6-7ff6-4fe2-b778-06a5e99b2de5
-- title:
--   Is Pt Der: map sq
-- statement:
--   The Is Pt Der construction uses the map sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L68-L75

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

theorem ReciprocityTheory.PGsh.IsPtDer.map_sq {δ : A →ₗ[R] R} (hδ : IsPtDer δ) {f : A}
    (hf : f ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2) : δ f = 0 := by sorry
