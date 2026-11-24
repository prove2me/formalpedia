-- Prove2me | Theorems.Thm_PhosphorylationSharpness_reconstruct_totals
-- name    : PhosphorylationSharpness.reconstruct_totals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:23:05.070054+00:00
-- url     : https://prove2.me/theorems/3316ce44-f365-488e-8b72-32ef1278d731
-- title:
--   Phosphorylation Sharpness: reconstruct totals
-- statement:
--   The Phosphorylation Sharpness construction uses the reconstruct totals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Source.lean#L115-L134
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Source.lean#L115-L134

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Source
set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open scoped BigOperators

theorem PhosphorylationSharpness.reconstruct_totals {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ) :
    totalE (reconstruct t B D u s f)=u*f*(1+s*inventory B u) ∧
    totalF (reconstruct t B D u s f)=f*(1+s*u*inventory D u) ∧
    totalS (reconstruct t B D u s f)=s*inventory t u+u*s*f*(inventory B u+inventory D u) := by sorry
