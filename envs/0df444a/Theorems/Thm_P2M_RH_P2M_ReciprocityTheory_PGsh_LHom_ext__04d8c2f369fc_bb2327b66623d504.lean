-- Prove2me | Theorems.Thm_P2M_RH_P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc_bb2327b66623d504
-- name    : P2M_RH_P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc_bb2327b66623d504
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:29.564746+00:00
-- url     : https://prove2.me/theorems/fe6de27d-acee-4157-8880-be3ea4d2ddd6
-- title:
--   P2 M RH P2 M Reciprocity Theory PGsh LHom ext  04d8c2f369fc bb2327b66623d504: P2 M RH P2 M Reciprocity Theory PGsh LHom ext  04d8c2f369fc bb2327b66623d504
-- statement:
--   The P2 M RH P2 M Reciprocity Theory PGsh LHom ext  04d8c2f369fc bb2327b66623d504 construction uses the P2 M RH P2 M Reciprocity Theory PGsh LHom ext  04d8c2f369fc bb2327b66623d504 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L13-L14

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

theorem P2M_RH_P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc_bb2327b66623d504 {R S : LAlg R₀} {f g : LHom R S} (h : ∀ a, f.1 a = g.1 a) : f = g := by sorry

alias «ReciprocityTheory».«PGsh».«LHom».«ext'» := P2M_RH_P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc_bb2327b66623d504
