-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_U3_pow_mem__9e39d2041606
-- name    : P2M_ReciprocityTheory_PGsh_Up_U3_pow_mem__9e39d2041606
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:40.791574+00:00
-- url     : https://prove2.me/theorems/6b58fe5d-6544-4b9b-a101-58947b5c76c6
-- title:
--   P2 M Reciprocity Theory PGsh Up U3 pow mem  9e39d2041606: P2 M Reciprocity Theory PGsh Up U3 pow mem  9e39d2041606
-- statement:
--   The P2 M Reciprocity Theory PGsh Up U3 pow mem  9e39d2041606 construction uses the P2 M Reciprocity Theory PGsh Up U3 pow mem  9e39d2041606 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L162-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L162-L170

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

theorem P2M_ReciprocityTheory_PGsh_Up_U3_pow_mem__9e39d2041606 (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C} (hf : f ∈ AA.carrier)
    (n : ℕ) : f ^ n ∈ AA.carrier := by sorry

alias «ReciprocityTheory».«PGsh».«Up».«U3».«pow_mem'» := P2M_ReciprocityTheory_PGsh_Up_U3_pow_mem__9e39d2041606
