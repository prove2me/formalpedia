-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc
-- name    : P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:41.425407+00:00
-- url     : https://prove2.me/theorems/af5188e1-60c2-4e29-a906-b6f6053fcbaf
-- title:
--   P2 M Reciprocity Theory PGsh LHom ext  04d8c2f369fc: P2 M Reciprocity Theory PGsh LHom ext  04d8c2f369fc
-- statement:
--   The P2 M Reciprocity Theory PGsh LHom ext  04d8c2f369fc construction uses the P2 M Reciprocity Theory PGsh LHom ext  04d8c2f369fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsFibreSq.lean#L11-L12

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

theorem P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc {R S : LAlg R₀} {f g : LHom R S} (h : ∀ x, f.1 x = g.1 x) : f = g := by sorry

alias «ReciprocityTheory».«PGsh».«LHom».«ext'» := P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc
