-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_dualLat_dualLat_spanCols
-- name    : ReciprocityTheory.PGsh.L2.dualLat_dualLat_spanCols
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:05:43.69937+00:00
-- url     : https://prove2.me/theorems/b3a917d1-92d2-408f-99ab-a596dab2e710
-- title:
--   L2: dual Lat dual Lat span Cols
-- statement:
--   The L2 construction uses the dual Lat dual Lat span Cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetEqOfSpanEq.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetEqOfSpanEq.lean#L62-L69

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X : Type} [Fintype X] [DecidableEq X]

theorem ReciprocityTheory.PGsh.L2.dualLat_dualLat_spanCols (B : Matrix X X C) (hB : IsUnit B.det) :
    dualLat (dualLat (Submodule.span R (Set.range fun j x => B x j))) =
      Submodule.span R (Set.range fun j x => B x j) := by sorry
