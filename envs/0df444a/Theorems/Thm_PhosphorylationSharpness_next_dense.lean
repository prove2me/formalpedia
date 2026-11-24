-- Prove2me | Theorems.Thm_PhosphorylationSharpness_next_dense
-- name    : PhosphorylationSharpness.next_dense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:20:23.495723+00:00
-- url     : https://prove2.me/theorems/3f5eaf0f-ea31-4663-aa7e-be1603947c9b
-- title:
--   Phosphorylation Sharpness: next dense
-- statement:
--   The Phosphorylation Sharpness construction uses the next dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Recurrence.lean#L58-L67
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Recurrence.lean#L58-L67

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial

theorem PhosphorylationSharpness.next_dense {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m)
    {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    DensePositive (nextN a b p q) (m+1) ∧
      DensePositive (nextJ a b p q) (m+1) := by sorry
