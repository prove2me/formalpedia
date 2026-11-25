-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_Tot_sum_mulVec__b7773400bc89
-- name    : P2M_ReciprocityTheory_PGsh_Up_Tot_sum_mulVec__b7773400bc89
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:45.728545+00:00
-- url     : https://prove2.me/theorems/6d55db5e-6e3c-5f2b-9c80-e30f99ce70e6
-- title:
--   P2 M Reciprocity Theory PGsh Up Tot sum mul Vec  b7773400bc89: P2 M Reciprocity Theory PGsh Up Tot sum mul Vec  b7773400bc89
-- statement:
--   The P2 M Reciprocity Theory PGsh Up Tot sum mul Vec  b7773400bc89 construction uses the P2 M Reciprocity Theory PGsh Up Tot sum mul Vec  b7773400bc89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigenLengthProductStatementHolds.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigenLengthProductStatementHolds.lean#L51-L56

import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthFrobeniusStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthProductStatementHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.Up.Tot
variable {R : Type} [CommRing R]

theorem P2M_ReciprocityTheory_PGsh_Up_Tot_sum_mulVec__b7773400bc89 {n : Type} [Fintype n] {ι : Type} (s : Finset ι) (A : ι → Matrix n n R)
    (w : n → R) : (∑ i ∈ s, A i) *ᵥ w = ∑ i ∈ s, A i *ᵥ w := by sorry

alias «ReciprocityTheory».«PGsh».«Up».«Tot».«sum_mulVec'» := P2M_ReciprocityTheory_PGsh_Up_Tot_sum_mulVec__b7773400bc89
