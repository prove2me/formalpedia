-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_p__sqZero_400d97111e57
-- name    : P2M_ReciprocityTheory_PGsh_p__sqZero_400d97111e57
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:18:49.588797+00:00
-- url     : https://prove2.me/theorems/305068f3-974f-55d3-8974-b392b9f83ca8
-- title:
--   P2 M Reciprocity Theory PGsh p  sq Zero 400d97111e57: P2 M Reciprocity Theory PGsh p  sq Zero 400d97111e57
-- statement:
--   The P2 M Reciprocity Theory PGsh p  sq Zero 400d97111e57 construction uses the P2 M Reciprocity Theory PGsh p  sq Zero 400d97111e57 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L143-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SmKerSurj.lean#L143-L164

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

theorem P2M_ReciprocityTheory_PGsh_p__sqZero_400d97111e57 : (FP.p₁ π Dp.π).SqZero := by sorry

alias «ReciprocityTheory».«PGsh».«p₁_sqZero» := P2M_ReciprocityTheory_PGsh_p__sqZero_400d97111e57
