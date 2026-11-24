-- Prove2me | Theorems.Thm_PhosphorylationSharpness_DensePositive_scaled_limit
-- name    : PhosphorylationSharpness.DensePositive.scaled_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:21:26.136075+00:00
-- url     : https://prove2.me/theorems/74b801c5-80c6-45fa-80c0-b58396d93a92
-- title:
--   Dense Positive: scaled limit
-- statement:
--   The Dense Positive construction uses the scaled limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Conversion.lean#L22-L31
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Conversion.lean#L22-L31

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology

theorem PhosphorylationSharpness.DensePositive.scaled_limit {p : ℝ[X]} {m : ℕ} (hp : DensePositive p m) :
    Tendsto (fun r : ℝ => p.eval r / r^m) atTop (𝓝 (p.coeff m)) := by sorry
