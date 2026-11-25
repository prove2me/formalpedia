-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_lam_omega_mem
-- name    : ReciprocityTheory.PGsh.Up.U3.lam_omega_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:31.806886+00:00
-- url     : https://prove2.me/theorems/32dac82b-a6b8-46b1-b946-f15c3b3b715d
-- title:
--   U3: lam omega mem
-- statement:
--   The U3 construction uses the lam omega mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L214-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L214-L232

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
variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem ReciprocityTheory.PGsh.Up.U3.lam_omega_mem (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C}
    (hf : f ∈ AA.carrier) : (fun t => lam ω f * ω t) ∈ AA.carrier := by sorry
