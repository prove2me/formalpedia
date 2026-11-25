-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_span_eq_of_vdet_eq
-- name    : ReciprocityTheory.PGsh.Up.U3.span_eq_of_vdet_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:24.23671+00:00
-- url     : https://prove2.me/theorems/b8072aa5-80df-4d61-af1e-a690c905e11c
-- title:
--   U3: span eq of vdet eq
-- statement:
--   The U3 construction uses the span eq of vdet eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VdetLeOfSpanLe.lean#L31-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VdetLeOfSpanLe.lean#L31-L61

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_VdetLeOfSpanLe
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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {X : Type} [Fintype X] [DecidableEq X]

theorem ReciprocityTheory.PGsh.Up.U3.span_eq_of_vdet_eq (hv : v.Integers R) {B B' : Matrix X X C} (hB' : IsUnit B'.det)
    (hle : Submodule.span R (Set.range fun j x => B x j) ≤
      Submodule.span R (Set.range fun j x => B' x j)) (hdet : v B.det = v B'.det) :
    Submodule.span R (Set.range fun j x => B x j) =
      Submodule.span R (Set.range fun j x => B' x j) := by sorry
