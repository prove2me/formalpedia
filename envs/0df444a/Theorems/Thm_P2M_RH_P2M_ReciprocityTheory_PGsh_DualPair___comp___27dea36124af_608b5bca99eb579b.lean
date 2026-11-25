-- Prove2me | Theorems.Thm_P2M_RH_P2M_ReciprocityTheory_PGsh_DualPair___comp___27dea36124af_608b5bca99eb579b
-- name    : P2M_RH_P2M_ReciprocityTheory_PGsh_DualPair___comp___27dea36124af_608b5bca99eb579b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:11:22.460668+00:00
-- url     : https://prove2.me/theorems/110e8ee6-3410-4361-bf65-3067cfc457de
-- title:
--   P2 M RH P2 M Reciprocity Theory PGsh Dual Pair   comp   27dea36124af 608b5bca99eb579b: P2 M RH P2 M Reciprocity Theory PGsh Dual Pair   comp   27dea36124af 608b5bca99eb579b
-- statement:
--   The P2 M RH P2 M Reciprocity Theory PGsh Dual Pair   comp   27dea36124af 608b5bca99eb579b construction uses the P2 M RH P2 M Reciprocity Theory PGsh Dual Pair   comp   27dea36124af 608b5bca99eb579b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L252-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L252-L252

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

theorem P2M_RH_P2M_ReciprocityTheory_PGsh_DualPair___comp___27dea36124af_608b5bca99eb579b : Dp.π.comp Dp.σ = LHom.id R := by sorry

alias «ReciprocityTheory».«PGsh».«DualPair».«π_comp_σ» := P2M_RH_P2M_ReciprocityTheory_PGsh_DualPair___comp___27dea36124af_608b5bca99eb579b
