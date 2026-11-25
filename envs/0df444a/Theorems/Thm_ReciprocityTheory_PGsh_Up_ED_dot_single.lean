-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_ED_dot_single
-- name    : ReciprocityTheory.PGsh.Up.ED.dot_single
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:06:21.940348+00:00
-- url     : https://prove2.me/theorems/b094e647-ead0-50d9-8d54-7575f403884c
-- title:
--   ED: dot single
-- statement:
--   The ED construction uses the dot single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DotSingle.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DotSingle.lean#L13-L23

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

theorem ReciprocityTheory.PGsh.Up.ED.dot_single {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → R) →ₗ[R] R) (x : ι → R) :
    (fun k => f (Pi.single k 1)) ⬝ᵥ x = f x := by sorry
