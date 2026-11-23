-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_smul_cancel
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusGroupField.smul_cancel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:06.084216+00:00
-- url     : https://prove2.me/theorems/2b3390fa-95bd-44e2-879c-6018b556fcbb
-- title:
--   Frobenius Group Field: smul cancel
-- statement:
--   The Frobenius Group Field construction uses the smul cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigPowEqOne.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigPowEqOne.lean#L11-L25

import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem
import Definitions.Def_ReciprocityTheory_DualLattices_EigPowEqOne
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

theorem ReciprocityTheory.PGsh.Up.FrobeniusGroupField.smul_cancel (hv : v.Integers R) {n : Type} {e : Matrix n n R} (he : e ≠ 0) {x y : R}
    (h : x • e = y • e) : x = y := by sorry
