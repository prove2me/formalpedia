-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_pow_pred
-- name    : ReciprocityTheory.PGsh.Up.U3.IsTeich.pow_pred
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:07:48.820616+00:00
-- url     : https://prove2.me/theorems/71b7d850-0cf5-4a1e-b6d6-896c8f5a6333
-- title:
--   Is Teich: pow pred
-- statement:
--   The Is Teich construction uses the pow pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L46-L51

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

theorem ReciprocityTheory.PGsh.Up.U3.IsTeich.pow_pred {a : ZMod p} (ha : a ≠ 0) : ω a ^ (p - 1) = 1 := by sorry
