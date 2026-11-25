-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_valuation_det_eq_of_span_eq
-- name    : ReciprocityTheory.PGsh.L2.valuation_det_eq_of_span_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:49.480501+00:00
-- url     : https://prove2.me/theorems/304ca9c1-7100-5112-9963-b3fa51679c07
-- title:
--   L2: valuation det eq of span eq
-- statement:
--   The L2 construction uses the valuation det eq of span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetEqOfSpanEq.lean#L78-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetEqOfSpanEq.lean#L78-L97

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

theorem ReciprocityTheory.PGsh.L2.valuation_det_eq_of_span_eq (v : Valuation C NNReal) (hv : v.Integers R)
    (B B' : Matrix X X C)
    (h : Submodule.span R (Set.range fun j x => B x j) =
      Submodule.span R (Set.range fun j x => B' x j)) : v B.det = v B'.det := by sorry
