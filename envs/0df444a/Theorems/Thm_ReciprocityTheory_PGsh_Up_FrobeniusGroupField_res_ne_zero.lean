-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_res_ne_zero
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusGroupField.res_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:07:45.360802+00:00
-- url     : https://prove2.me/theorems/6b52d5cd-579e-48b6-a356-38248d054a45
-- title:
--   Frobenius Group Field: res ne zero
-- statement:
--   The Frobenius Group Field construction uses the res ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitOfNotMem.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitOfNotMem.lean#L50-L51

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

theorem ReciprocityTheory.PGsh.Up.FrobeniusGroupField.res_ne_zero (hv : v.Integers R) (r : R) : res hv r ≠ 0 ↔ v (algebraMap R C r) = 1 := by sorry
