-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_mr_comp___1e468da7d874
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_mr_comp___1e468da7d874
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:48.962063+00:00
-- url     : https://prove2.me/theorems/26389fb6-487f-544f-b5f1-45289db322d9
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair mr comp   1e468da7d874: P2 M Reciprocity Theory PGsh Dual Pair mr comp   1e468da7d874
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair mr comp   1e468da7d874 construction uses the P2 M Reciprocity Theory PGsh Dual Pair mr comp   1e468da7d874 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L156-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L156-L159

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
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
open ReciprocityTheory.PGsh.DualPair
variable {R : LAlg R₀} (Dp : DualPair R)

theorem P2M_ReciprocityTheory_PGsh_DualPair_mr_comp___1e468da7d874 (r : (R : Type u)) : (Dp.mr r).comp Dp.σ = Dp.σ := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«mr_comp_σ» := P2M_ReciprocityTheory_PGsh_DualPair_mr_comp___1e468da7d874
