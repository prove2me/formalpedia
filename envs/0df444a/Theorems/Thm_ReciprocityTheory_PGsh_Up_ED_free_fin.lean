-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_ED_free_fin
-- name    : ReciprocityTheory.PGsh.Up.ED.free_fin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:07:54.077736+00:00
-- url     : https://prove2.me/theorems/c7b30e84-7500-4556-a7f7-f10ac6cfba04
-- title:
--   ED: free fin
-- statement:
--   The ED construction uses the free fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ElementaryDivisorStatement.lean#L18-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ElementaryDivisorStatement.lean#L18-L39

import Definitions.Def_ReciprocityTheory_DualLattices_DotSingle
import Definitions.Def_ReciprocityTheory_DualLattices_EmbeddingSeparatingGroupStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthProductStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ElementaryDivisorStatement
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
open ReciprocityTheory.PGsh.L2
open ReciprocityTheory.PGsh.Up.ED
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.ED.free_fin (hv : v.Integers R) {α : Type} [Fintype α] (S : Submodule R (α → R)) (hS : S.FG) :
    Module.Free R S ∧ Module.Finite R S := by sorry
