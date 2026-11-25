-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_BX_tw__r_c0cc6876c9a8
-- name    : P2M_ReciprocityTheory_PGsh_BX_tw__r_c0cc6876c9a8
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:17:46.082119+00:00
-- url     : https://prove2.me/theorems/178a37a8-ce68-57d2-8149-d325cd8cb9f5
-- title:
--   P2 M Reciprocity Theory PGsh BX tw  r c0cc6876c9a8: P2 M Reciprocity Theory PGsh BX tw  r c0cc6876c9a8
-- statement:
--   The P2 M Reciprocity Theory PGsh BX tw  r c0cc6876c9a8 construction uses the P2 M Reciprocity Theory PGsh BX tw  r c0cc6876c9a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsLimTensor.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsLimTensor.lean#L17-L21

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulKerZero
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsLimTensor
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
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {p : ℕ}

theorem P2M_ReciprocityTheory_PGsh_BX_tw__r_c0cc6876c9a8 (Tw : ATowerL R₀ p) (n : ℕ) : (Tw.π n).comp (Tw.r' n) = (Tw.r n).comp (Tw.π (n + 1)) := by sorry

alias «ReciprocityTheory».«PGsh».«BX».«tw_πr» := P2M_ReciprocityTheory_PGsh_BX_tw__r_c0cc6876c9a8
