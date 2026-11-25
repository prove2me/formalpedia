-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_fr_comp___e46f679c4983
-- name    : P2M_ReciprocityTheory_PGsh_DualPair_fr_comp___e46f679c4983
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:49.109949+00:00
-- url     : https://prove2.me/theorems/37d69faa-5cdd-41ab-a3f9-fb6e426b5b2d
-- title:
--   P2 M Reciprocity Theory PGsh Dual Pair fr comp   e46f679c4983: P2 M Reciprocity Theory PGsh Dual Pair fr comp   e46f679c4983
-- statement:
--   The P2 M Reciprocity Theory PGsh Dual Pair fr comp   e46f679c4983 construction uses the P2 M Reciprocity Theory PGsh Dual Pair fr comp   e46f679c4983 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L241-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L241-L243

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
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

theorem P2M_ReciprocityTheory_PGsh_DualPair_fr_comp___e46f679c4983 (r : (R : Type u)) : (Dp.fr r).comp Dp.σ = Dp.σ := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«fr_comp_σ» := P2M_ReciprocityTheory_PGsh_DualPair_fr_comp___e46f679c4983
