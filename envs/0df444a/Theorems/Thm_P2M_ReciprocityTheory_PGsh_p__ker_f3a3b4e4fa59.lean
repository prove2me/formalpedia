-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_p__ker_f3a3b4e4fa59
-- name    : P2M_ReciprocityTheory_PGsh_p__ker_f3a3b4e4fa59
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:18.767583+00:00
-- url     : https://prove2.me/theorems/73340f15-7695-5c9d-8a11-4ec146071b0c
-- title:
--   P2 M Reciprocity Theory PGsh p  ker f3a3b4e4fa59: P2 M Reciprocity Theory PGsh p  ker f3a3b4e4fa59
-- statement:
--   The P2 M Reciprocity Theory PGsh p  ker f3a3b4e4fa59 construction uses the P2 M Reciprocity Theory PGsh p  ker f3a3b4e4fa59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L166-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L166-L170

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

theorem P2M_ReciprocityTheory_PGsh_p__ker_f3a3b4e4fa59 : ∀ a ∈ (FP.p₁ π Dp.π).ker, (FP.p₂ π Dp.π).1.toLinearMap a ∈ Dp.π.ker := by sorry

alias «ReciprocityTheory».«PGsh».«p₂_ker» := P2M_ReciprocityTheory_PGsh_p__ker_f3a3b4e4fa59
