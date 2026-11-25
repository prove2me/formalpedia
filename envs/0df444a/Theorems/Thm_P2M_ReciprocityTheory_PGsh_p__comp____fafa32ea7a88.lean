-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_p__comp____fafa32ea7a88
-- name    : P2M_ReciprocityTheory_PGsh_p__comp____fafa32ea7a88
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:12.795603+00:00
-- url     : https://prove2.me/theorems/464cdcd2-4dff-5135-9240-c54e2c914ca8
-- title:
--   P2 M Reciprocity Theory PGsh p  comp    fafa32ea7a88: P2 M Reciprocity Theory PGsh p  comp    fafa32ea7a88
-- statement:
--   The P2 M Reciprocity Theory PGsh p  comp    fafa32ea7a88 construction uses the P2 M Reciprocity Theory PGsh p  comp    fafa32ea7a88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L130-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L130-L130

import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
variable {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R)

theorem P2M_ReciprocityTheory_PGsh_p__comp____fafa32ea7a88 : (FP.p₁ π Dp.π).comp (ι₁ π Dp) = LHom.id R' := by sorry

alias «ReciprocityTheory».«PGsh».«p₁_comp_ι₁» := P2M_ReciprocityTheory_PGsh_p__comp____fafa32ea7a88
