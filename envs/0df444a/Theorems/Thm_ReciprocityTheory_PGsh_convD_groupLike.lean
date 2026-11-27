-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_convD_groupLike
-- name    : ReciprocityTheory.PGsh.convD_groupLike
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:37:17.139462+00:00
-- url     : https://prove2.me/theorems/fb8b6d8a-0e1b-5605-bbf3-e6a1145c3585
-- title:
--   PGsh: conv D group Like
-- statement:
--   The PGsh construction uses the conv D group Like property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L59-L61

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

theorem ReciprocityTheory.PGsh.convD_groupLike (δ : A →ₗ[R] R) {χ : A} (h : IsGroupLikeElem R χ) :
    convD δ χ = δ χ • χ := by sorry
