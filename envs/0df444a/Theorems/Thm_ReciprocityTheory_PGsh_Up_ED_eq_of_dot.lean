-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_ED_eq_of_dot
-- name    : ReciprocityTheory.PGsh.Up.ED.eq_of_dot
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:07:10.883279+00:00
-- url     : https://prove2.me/theorems/d4080462-fc9c-54e1-9d4a-feaab27f8f56
-- title:
--   ED: eq of dot
-- statement:
--   The ED construction uses the eq of dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DotSingle.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DotSingle.lean#L25-L28

import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsSmulMemOfMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_DotSingle
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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.ED
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.ED.eq_of_dot {ι : Type} [Fintype ι] [DecidableEq ι] {w w' : ι → R}
    (h : ∀ x, w ⬝ᵥ x = w' ⬝ᵥ x) : w = w' := by sorry
