-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_val_prim_root
-- name    : ReciprocityTheory.PGsh.Up.U3.val_prim_root
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:28.980139+00:00
-- url     : https://prove2.me/theorems/b8c3b2df-9ec6-4377-adaf-ea5214032edb
-- title:
--   U3: val prim root
-- statement:
--   The U3 construction uses the val prim root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VIntCastLtOneOfDvd.lean#L230-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VIntCastLtOneOfDvd.lean#L230-L242

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

theorem ReciprocityTheory.PGsh.Up.U3.val_prim_root {z : C} (hz : IsPrimitiveRoot z p) : v (z - 1) ^ (p - 1) = v (p : C) := by sorry
