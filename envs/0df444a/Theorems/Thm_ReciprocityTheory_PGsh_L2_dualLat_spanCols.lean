-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_dualLat_spanCols
-- name    : ReciprocityTheory.PGsh.L2.dualLat_spanCols
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:27.606251+00:00
-- url     : https://prove2.me/theorems/2cb8d310-1fe6-4f7e-9961-49ca2a0b6656
-- title:
--   L2: dual Lat span Cols
-- statement:
--   The L2 construction uses the dual Lat span Cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetEqOfSpanEq.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetEqOfSpanEq.lean#L52-L60

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

theorem ReciprocityTheory.PGsh.L2.dualLat_spanCols (B : Matrix X X C) (hB : IsUnit B.det) :
    dualLat (Submodule.span R (Set.range fun j x => B x j)) =
      Submodule.span R (Set.range fun j x => (B⁻¹)ᵀ x j) := by sorry
