-- Prove2me | Theorems.Thm_PhosphorylationSharpness_pair_roots
-- name    : PhosphorylationSharpness.pair_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:20:17.531218+00:00
-- url     : https://prove2.me/theorems/3276630f-8847-4702-a8df-52c8314ef52d
-- title:
--   Phosphorylation Sharpness: pair roots
-- statement:
--   The Phosphorylation Sharpness construction uses the pair roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Recurrence.lean#L95-L110
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Recurrence.lean#L95-L110

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial

theorem PhosphorylationSharpness.pair_roots (m j : ℕ) (hj : j ≤ 2*m) :
    ((j:ℝ)+2-1)*(pair m).1.eval (ratio ((j:ℝ)+2)) -
      2*(pair m).2.eval (ratio ((j:ℝ)+2)) = 0 := by sorry
