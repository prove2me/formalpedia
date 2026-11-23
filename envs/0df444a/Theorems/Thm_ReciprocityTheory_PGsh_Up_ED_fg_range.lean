-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_ED_fg_range
-- name    : ReciprocityTheory.PGsh.Up.ED.fg_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:33.18511+00:00
-- url     : https://prove2.me/theorems/5c03d2e5-8a1e-42aa-bed0-388fdf9ff65b
-- title:
--   ED: fg range
-- statement:
--   The ED construction uses the fg range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ElementaryDivisorStatement.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ElementaryDivisorStatement.lean#L41-L44

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

theorem ReciprocityTheory.PGsh.Up.ED.fg_range {α β : Type} [Fintype α] [Fintype β] (A : Matrix β α R) :
    (LinearMap.range (Matrix.mulVecLin A)).FG := by sorry
