-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_idem_eq_zero
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusGroupField.idem_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:06:52.097356+00:00
-- url     : https://prove2.me/theorems/5e6a8ef4-b58b-4fca-83eb-86472716529f
-- title:
--   Frobenius Group Field: idem eq zero
-- statement:
--   The Frobenius Group Field construction uses the idem eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitOfNotMem.lean#L63-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitOfNotMem.lean#L63-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem
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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.FrobeniusGroupField.idem_eq_zero (hv : v.Integers R) {n : Type} [Fintype n] [DecidableEq n]
    (e : Matrix n n R) (he : e * e = e) (hm : ∀ a b, e a b ∈ mI hv) : e = 0 := by sorry
