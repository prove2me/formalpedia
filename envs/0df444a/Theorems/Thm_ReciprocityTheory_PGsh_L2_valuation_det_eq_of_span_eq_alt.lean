-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_valuation_det_eq_of_span_eq_alt
-- name    : ReciprocityTheory.PGsh.L2.valuation_det_eq_of_span_eq_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:57.899128+00:00
-- url     : https://prove2.me/theorems/ab827a0d-d30d-48ce-97d0-d67b86ec3540
-- title:
--   L2: valuation det eq of span eq alt
-- statement:
--   The L2 construction uses the valuation det eq of span eq alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitDetOfSpanEq.lean#L37-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitDetOfSpanEq.lean#L37-L57

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

theorem ReciprocityTheory.PGsh.L2.valuation_det_eq_of_span_eq_alt (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    {P Q : Matrix X X C} (hP : IsUnit P.det)
    (h : Submodule.span R (Set.range fun j x => P x j) =
      Submodule.span R (Set.range fun j x => Q x j)) :
    v Q.det = v P.det := by sorry
