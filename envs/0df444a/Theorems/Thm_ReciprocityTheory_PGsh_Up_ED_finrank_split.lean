-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_ED_finrank_split
-- name    : ReciprocityTheory.PGsh.Up.ED.finrank_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:15:51.749112+00:00
-- url     : https://prove2.me/theorems/54fa4357-1310-4794-9174-3096e2fb6733
-- title:
--   ED: finrank split
-- statement:
--   The ED construction uses the finrank split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ElementaryDivisorStatement.lean#L46-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ElementaryDivisorStatement.lean#L46-L91

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

theorem ReciprocityTheory.PGsh.Up.ED.finrank_split (hv : v.Integers R) {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (P : Fin m → Matrix α α R) (horth : ∀ i j, P i * P j = if i = j then P i else 0)
    (hsum : ∑ i, P i = 1) :
    ∑ i, Module.finrank R (LinearMap.range (Matrix.mulVecLin (P i))) = Fintype.card α := by sorry
