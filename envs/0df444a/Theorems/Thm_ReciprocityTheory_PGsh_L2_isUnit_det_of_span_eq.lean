-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_isUnit_det_of_span_eq
-- name    : ReciprocityTheory.PGsh.L2.isUnit_det_of_span_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:33.801458+00:00
-- url     : https://prove2.me/theorems/be69bdf6-a008-551e-821e-c79668ef63e1
-- title:
--   L2: is Unit det of span eq
-- statement:
--   The L2 construction uses the is Unit det of span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitDetOfSpanEq.lean#L200-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitDetOfSpanEq.lean#L200-L207

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}

theorem ReciprocityTheory.PGsh.L2.isUnit_det_of_span_eq (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    {P Q : Matrix X X C} (hP : IsUnit P.det)
    (h : Submodule.span R (Set.range fun j x => P x j) =
      Submodule.span R (Set.range fun j x => Q x j)) : IsUnit Q.det := by sorry
