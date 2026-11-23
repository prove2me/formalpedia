-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_res_eq_zero
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusGroupField.res_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:09.538869+00:00
-- url     : https://prove2.me/theorems/b33ed8ce-409a-42b7-a5e2-f09785ee72c0
-- title:
--   Frobenius Group Field: res eq zero
-- statement:
--   The Frobenius Group Field construction uses the res eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitOfNotMem.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitOfNotMem.lean#L47-L48

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

theorem ReciprocityTheory.PGsh.Up.FrobeniusGroupField.res_eq_zero (hv : v.Integers R) (r : R) : res hv r = 0 ↔ v (algebraMap R C r) < 1 := by sorry
