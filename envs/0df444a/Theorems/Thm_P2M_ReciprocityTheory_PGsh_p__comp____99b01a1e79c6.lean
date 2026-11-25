-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_p__comp____99b01a1e79c6
-- name    : P2M_ReciprocityTheory_PGsh_p__comp____99b01a1e79c6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:07.30439+00:00
-- url     : https://prove2.me/theorems/fceca034-36a2-53e4-b499-e5cb5166567c
-- title:
--   P2 M Reciprocity Theory PGsh p  comp    99b01a1e79c6: P2 M Reciprocity Theory PGsh p  comp    99b01a1e79c6
-- statement:
--   The P2 M Reciprocity Theory PGsh p  comp    99b01a1e79c6 construction uses the P2 M Reciprocity Theory PGsh p  comp    99b01a1e79c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L132-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L132-L132

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

theorem P2M_ReciprocityTheory_PGsh_p__comp____99b01a1e79c6 : (FP.p₂ π Dp.π).comp (ι₁ π Dp) = Dp.σ.comp π := by sorry

alias «ReciprocityTheory».«PGsh».«p₂_comp_ι₁» := P2M_ReciprocityTheory_PGsh_p__comp____99b01a1e79c6
