-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_span_mk_top
-- name    : ReciprocityTheory.PGsh.Up.span_mk_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:06.844682+00:00
-- url     : https://prove2.me/theorems/1e525723-8c7d-4492-ac39-93468196757c
-- title:
--   Up: span mk top
-- statement:
--   The Up construction uses the span mk top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLowerBoundOf.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLowerBoundOf.lean#L85-L89

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
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

theorem ReciprocityTheory.PGsh.Up.span_mk_top {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M)
    {d : ℕ} (y : Fin d → M) (hy : Submodule.span R (Set.range y) = ⊤) :
    Submodule.span R (Set.range fun k => (Submodule.Quotient.mk (y k) : M ⧸ N)) = ⊤ := by sorry
