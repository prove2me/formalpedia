-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_scale_mem
-- name    : ReciprocityTheory.PGsh.Up.U3.scale_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:06.612027+00:00
-- url     : https://prove2.me/theorems/753f8eae-6141-45c8-9058-4e7b4db198fd
-- title:
--   U3: scale mem
-- statement:
--   The U3 construction uses the scale mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L173-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L173-L209

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
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
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
variable (hv : v.Integers R)
include hv
omit hv

theorem ReciprocityTheory.PGsh.Up.U3.scale_mem (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C} (hf : f ∈ AA.carrier)
    (b : ZMod p) : (fun t => f (b * t)) ∈ AA.carrier := by sorry
