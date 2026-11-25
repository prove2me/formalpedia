-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_lam_sum
-- name    : ReciprocityTheory.PGsh.Up.U3.lam_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:46.849427+00:00
-- url     : https://prove2.me/theorems/49f693b5-328c-5872-b46d-5a872697774e
-- title:
--   U3: lam sum
-- statement:
--   The U3 construction uses the lam sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L139-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L139-L145

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

theorem ReciprocityTheory.PGsh.Up.U3.lam_sum (ω : ZMod p → C) {ι : Type} [Fintype ι] (c : ι → C) (g : ι → ZMod p → C) :
    lam ω (fun a => ∑ j, c j * g j a) = ∑ j, c j * lam ω (g j) := by sorry
