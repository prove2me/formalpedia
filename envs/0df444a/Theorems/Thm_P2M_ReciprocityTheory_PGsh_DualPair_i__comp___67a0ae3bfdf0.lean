-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_i__comp___67a0ae3bfdf0
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_i__comp___67a0ae3bfdf0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:43:07.436225+00:00
-- url     : https://prove2.me/theorems/8ca95b1f-a696-5915-a965-e5770ae088b0
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair i  comp   67a0ae3bfdf0: P2 M Reciprocity Theory PGsh Dual Pair i  comp   67a0ae3bfdf0
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair i  comp   67a0ae3bfdf0 construction uses the P2 M Reciprocity Theory PGsh Dual Pair i  comp   67a0ae3bfdf0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L182-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L182-L188

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

theorem P2M_ReciprocityTheory_PGsh_DualPair_i__comp___67a0ae3bfdf0 : Dp.i₂L.comp Dp.σ = Dp.i₁L.comp Dp.σ := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«i₂_comp_σ» := P2M_ReciprocityTheory_PGsh_DualPair_i__comp___67a0ae3bfdf0
