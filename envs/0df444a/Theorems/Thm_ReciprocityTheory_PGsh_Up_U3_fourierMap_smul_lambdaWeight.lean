-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_fourierMap_smul_lambdaWeight
-- name    : ReciprocityTheory.PGsh.Up.U3.fourierMap_smul_lambdaWeight
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:42.002253+00:00
-- url     : https://prove2.me/theorems/a75ddfa1-7c6d-58c6-b404-1c4d795d371b
-- title:
--   U3: fourier Map smul lambda Weight
-- statement:
--   The U3 construction uses the fourier Map smul lambda Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FourierMapSmulLambdaWeight.lean#L122-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FourierMapSmulLambdaWeight.lean#L122-L185

import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
import Definitions.Def_ReciprocityTheory_DualLattices_FourierMapSmulLambdaWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.U3.fourierMap_smul_lambdaWeight {ω : ZMod p → C} (hω : IsTeich v ω) {ζ : C}
    (e : ZMod p ≃ AddChar (ZMod p) C) (he2 : ∀ h a, e h a = ζ ^ (h * a).val) (c : C) :
    fourier (R := R) (fun h a => e h a) (fun a => c * u0 ω a) =
      fun h => (c * ∑ a, u0 ω a * ζ ^ a.val) * ω h := by sorry
