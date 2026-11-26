-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair___comp__L_ad60e1a2b4a5
-- name    : P2M_ReciprocityTheory_PGsh_DualPair___comp__L_ad60e1a2b4a5
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:43:27.246497+00:00
-- url     : https://prove2.me/theorems/6fb5a5a2-669b-4d70-835a-a75774e849d8
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair   comp  L ad60e1a2b4a5: P2 M Reciprocity Theory PGsh Dual Pair   comp  L ad60e1a2b4a5
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair   comp  L ad60e1a2b4a5 construction uses the P2 M Reciprocity Theory PGsh Dual Pair   comp  L ad60e1a2b4a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L83-L84

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)

theorem P2M_ReciprocityTheory_PGsh_DualPair___comp__L_ad60e1a2b4a5 (c : (R : Type u)) : Dp.π.comp (Dp.μL c) = Dp.π := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«π_comp_μL» := P2M_ReciprocityTheory_PGsh_DualPair___comp__L_ad60e1a2b4a5
