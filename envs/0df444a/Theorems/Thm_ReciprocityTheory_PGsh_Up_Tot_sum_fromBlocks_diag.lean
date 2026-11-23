-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_Tot_sum_fromBlocks_diag
-- name    : ReciprocityTheory.PGsh.Up.Tot.sum_fromBlocks_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:55.959803+00:00
-- url     : https://prove2.me/theorems/30ffb115-630f-4f05-9172-d4143c190378
-- title:
--   Tot: sum from Blocks diag
-- statement:
--   The Tot construction uses the sum from Blocks diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigenLengthProductStatementHolds.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigenLengthProductStatementHolds.lean#L41-L49

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

theorem ReciprocityTheory.PGsh.Up.Tot.sum_fromBlocks_diag {g : ℕ} {ι : Type} (s : Finset ι)
    (A D : ι → Matrix (Fin g) (Fin g) R) :
    ∑ i ∈ s, fromBlocks (A i) 0 0 (D i) = fromBlocks (∑ i ∈ s, A i) 0 0 (∑ i ∈ s, D i) := by sorry
