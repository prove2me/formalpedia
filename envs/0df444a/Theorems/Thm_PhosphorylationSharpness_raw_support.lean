-- Prove2me | Theorems.Thm_PhosphorylationSharpness_raw_support
-- name    : PhosphorylationSharpness.raw_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:22:29.105804+00:00
-- url     : https://prove2.me/theorems/4ae87c52-baad-46d4-8f2a-b37a79adb601
-- title:
--   Phosphorylation Sharpness: raw support
-- statement:
--   The Phosphorylation Sharpness construction uses the raw support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Conversion.lean#L127-L134
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Conversion.lean#L127-L134

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology

theorem PhosphorylationSharpness.raw_support {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (r : ℝ)
    (i : ℕ) (hi : m < i) :
    (rawD p q r).coeff i=0 ∧ (rawB p q r).coeff i=0 := by sorry
