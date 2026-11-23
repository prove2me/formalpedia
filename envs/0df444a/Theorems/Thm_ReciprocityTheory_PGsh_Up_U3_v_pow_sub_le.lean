-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_v_pow_sub_le
-- name    : ReciprocityTheory.PGsh.Up.U3.v_pow_sub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:36.739805+00:00
-- url     : https://prove2.me/theorems/787e4969-7ae6-427c-a148-a4478be06fd8
-- title:
--   U3: v pow sub le
-- statement:
--   The U3 construction uses the v pow sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VIntCastLtOneOfDvd.lean#L62-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VIntCastLtOneOfDvd.lean#L62-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
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
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.U3.v_pow_sub_le {r s : C} (hr : v r ≤ 1) (hs : v s ≤ 1) (i : ℕ) :
    v (r ^ i - s ^ i) ≤ v (r - s) := by sorry
