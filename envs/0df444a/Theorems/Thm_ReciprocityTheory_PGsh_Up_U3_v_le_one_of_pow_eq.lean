-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_v_le_one_of_pow_eq
-- name    : ReciprocityTheory.PGsh.Up.U3.v_le_one_of_pow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:30.819683+00:00
-- url     : https://prove2.me/theorems/74411f58-5557-49cf-83a2-5e64db512c5f
-- title:
--   U3: v le one of pow eq
-- statement:
--   The U3 construction uses the v le one of pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VIntCastLtOneOfDvd.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VIntCastLtOneOfDvd.lean#L54-L60

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

theorem ReciprocityTheory.PGsh.Up.U3.v_le_one_of_pow_eq {r : C} (hr : r ^ p = r) : v r ≤ 1 := by sorry
