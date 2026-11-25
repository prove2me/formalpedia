-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_cmul_mem
-- name    : ReciprocityTheory.PGsh.Up.U3.cmul_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:32.534947+00:00
-- url     : https://prove2.me/theorems/80d9acb1-9161-48ae-9183-499c3a22e39c
-- title:
--   U3: cmul mem
-- statement:
--   The U3 construction uses the cmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L152-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean#L152-L159

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

theorem ReciprocityTheory.PGsh.Up.U3.cmul_mem {X : Type} (M : Submodule R (X → C)) {c : C} (hc : v c ≤ 1) {f : X → C}
    (hf : f ∈ M) : (fun t => c * f t) ∈ M := by sorry
