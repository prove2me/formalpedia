-- Prove2me | Theorems.Thm_PhosphorylationSharpness_rawB_scaled_limit
-- name    : PhosphorylationSharpness.rawB_scaled_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:22:17.717737+00:00
-- url     : https://prove2.me/theorems/406264d8-8baf-4bb4-8814-6e421e9f5ef0
-- title:
--   Phosphorylation Sharpness: raw B scaled limit
-- statement:
--   The Phosphorylation Sharpness construction uses the raw B scaled limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Conversion.lean#L109-L125
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Conversion.lean#L109-L125

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology

theorem PhosphorylationSharpness.rawB_scaled_limit {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (i : ℕ) :
    Tendsto (fun r : ℝ => (rawB p q r).coeff i/r^(m+1)) atTop
      (𝓝 (4*p.coeff m*(q.coeff i+p.coeff i))) := by sorry
