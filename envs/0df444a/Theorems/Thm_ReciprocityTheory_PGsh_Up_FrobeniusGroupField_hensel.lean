-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_hensel
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusGroupField.hensel
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:06:25.693857+00:00
-- url     : https://prove2.me/theorems/a6a703e8-fe11-51ca-b1b3-b013e953384a
-- title:
--   Frobenius Group Field: hensel
-- statement:
--   The Frobenius Group Field construction uses the hensel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsAdicCompleteOfBasis.lean#L70-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsAdicCompleteOfBasis.lean#L70-L116

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

theorem ReciprocityTheory.PGsh.Up.FrobeniusGroupField.hensel (f : ℤ_[p][X]) (hf : f.Monic) {m : ℕ} (hm0 : 0 < m) (hmp : ¬ p ∣ m) (Q0 : ℤ_[p][X])
    (h0 : ∃ K : ℤ_[p][X], AdjoinRoot.mk f (Q0 ^ m - 1) = (p : AdjoinRoot f) * AdjoinRoot.mk f K) :
    ∃ Q K : ℤ_[p][X], f ∣ Q ^ m - 1 ∧
      AdjoinRoot.mk f (Q - Q0) = (p : AdjoinRoot f) * AdjoinRoot.mk f K := by sorry
