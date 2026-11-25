-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_ne_zero
-- name    : ReciprocityTheory.PGsh.Up.U3.IsTeich.ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:53.845741+00:00
-- url     : https://prove2.me/theorems/787f6659-7cfe-465a-b657-b44844df4391
-- title:
--   Is Teich: ne zero
-- statement:
--   The Is Teich construction uses the ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L40-L44

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

theorem ReciprocityTheory.PGsh.Up.U3.IsTeich.ne_zero {a : ZMod p} (ha : a ≠ 0) : ω a ≠ 0 := by sorry
