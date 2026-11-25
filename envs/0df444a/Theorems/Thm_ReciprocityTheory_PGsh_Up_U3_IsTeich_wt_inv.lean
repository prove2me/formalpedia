-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_wt_inv
-- name    : ReciprocityTheory.PGsh.Up.U3.IsTeich.wt_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:08.406722+00:00
-- url     : https://prove2.me/theorems/b5253f70-63fb-5d40-8074-3f9e81544688
-- title:
--   Is Teich: wt inv
-- statement:
--   The Is Teich construction uses the wt inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L87-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L87-L92

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
open ReciprocityTheory.PGsh.Up.U3.IsTeich
variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem ReciprocityTheory.PGsh.Up.U3.IsTeich.wt_inv {a : ZMod p} (ha : a ≠ 0) : wt ω a⁻¹ = ω a := by sorry
