-- Prove2me | Theorems.Thm_PhosphorylationSharpness_quotient_scaled_limit
-- name    : PhosphorylationSharpness.quotient_scaled_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:22:31.316918+00:00
-- url     : https://prove2.me/theorems/622d56d5-e578-4a44-b414-0ddca3a94d1c
-- title:
--   Phosphorylation Sharpness: quotient scaled limit
-- statement:
--   The Phosphorylation Sharpness construction uses the quotient scaled limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Conversion.lean#L77-L95
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Conversion.lean#L77-L95

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology

theorem PhosphorylationSharpness.quotient_scaled_limit {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (i : ℕ) :
    Tendsto (fun r : ℝ => (quotient p q r).coeff i / r^m) atTop
      (𝓝 (p.coeff m*q.coeff i)) := by sorry
