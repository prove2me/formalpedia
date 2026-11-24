-- Prove2me | Theorems.Thm_PhosphorylationSharpness_rawD_scaled_limit
-- name    : PhosphorylationSharpness.rawD_scaled_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:21:30.640159+00:00
-- url     : https://prove2.me/theorems/c8aeefb9-772a-46c4-a361-f7e2a51cd39d
-- title:
--   Phosphorylation Sharpness: raw D scaled limit
-- statement:
--   The Phosphorylation Sharpness construction uses the raw D scaled limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Conversion.lean#L102-L107
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Conversion.lean#L102-L107

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology

theorem PhosphorylationSharpness.rawD_scaled_limit {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (i : ℕ) :
    Tendsto (fun r : ℝ => (rawD p q r).coeff i/r^m) atTop
      (𝓝 (4*p.coeff m*q.coeff i)) := by sorry
