-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_finite_quot
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusGroupField.finite_quot
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:06:31.137144+00:00
-- url     : https://prove2.me/theorems/df30fff7-f480-5bac-baa4-754f3a23e369
-- title:
--   Frobenius Group Field: finite quot
-- statement:
--   The Frobenius Group Field construction uses the finite quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsAdicCompleteOfBasis.lean#L118-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsAdicCompleteOfBasis.lean#L118-L142

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {p : ℕ} [hp : Fact p.Prime]

theorem ReciprocityTheory.PGsh.Up.FrobeniusGroupField.finite_quot (f : ℤ_[p][X]) (hf : f.Monic) :
    Finite (AdjoinRoot f ⧸ Ideal.span {(p : AdjoinRoot f)}) := by sorry
