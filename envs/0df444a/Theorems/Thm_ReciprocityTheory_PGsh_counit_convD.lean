-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_counit_convD
-- name    : ReciprocityTheory.PGsh.counit_convD
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:32.344413+00:00
-- url     : https://prove2.me/theorems/4aea3c67-50e3-444f-9dbb-cc5820b788eb
-- title:
--   PGsh: counit conv D
-- statement:
--   The PGsh construction uses the counit conv D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L46-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L46-L57

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

theorem ReciprocityTheory.PGsh.counit_convD (δ : A →ₗ[R] R) (f : A) :
    Coalgebra.counit (R := R) (convD δ f) = δ f := by sorry
